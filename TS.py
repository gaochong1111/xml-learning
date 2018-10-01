from z3 import Bool, BoolVal, And, Or, Not, Implies

import time

class SentenceTranslator():
    """ Translator for tranlating a sentence into a formula.

    Properties:
        alphabet: Sigma
            For example: {"a", "b"}
        k: k-OA
            For example: 2
        var_list: all variable list
            For example: [True, V1, V2, ..., V25, False]
        id_table: str -> int, character map to ID
            For example: 
            {
                "a": 1,
                "b": 2
            }
        formula_determinstic: formula represent the deterministic property
            For example:
                And(Not(And(V6, V7)), ..., Not(And(V23, V24)))
        
        src_to_alphabet1_table: (0, id2) -> Bool
            For example:
                {
                    id2 -> True
                }
                tips:  1 represent src->a1: (0, *, 1, 1) -> 1(A1)
        alphabet1_to_alphabet_table: (id1, id2) -> Bool 
            For example:
                {
                    (id1, id2) -> True
                }
                tips: (1, 1)   represent a1->a_j: Or(A_(1, 1, 1, j))
        alphabet_to_alphabet_table: (id1, id2) -> Bool
            For example:
                {
                    (id1, id2) -> True
                }
                tips: (1, 1) represent a_m -> a_n: Or(A_(1, m, 1, n))
        alphabet_to_snk_table: (id1, len(alphabet)+1) -> Bool
            For example:
                {
                    id1 -> True
                }
                tips: 1 represent a_1 -> snk: Or(A_(1, m, 3, *))



        alphabet1_to_alphabet_imply_table: (id1, id2, id3) 
        character_1 -> character_2 -> character_3 
            For example:
                {
                    (id1, id2, id3) -> True
                }
                tips: (1, 1, 1) represent a -> a -> a: And_k2(Or(A_(1, 1, 1, k2)) -> Or(A_(1, k2, 1, k3))) 

        alphabet_to_alphabet_imply_table: (id1, id2, id3) 
        character_1 -> character_2 -> character_3 
            For example:
                {
                    (id1, id2, id3) -> True
                }
                tips: (1, 1, 1) represent a -> a -> a: And_k2(Or(A_(1, k1, 1, k2)) -> Or(A_(1, k2, 1, k3))) 

        alphabet_to_snk_imply_table: (id1, id2) 
        character_1 -> character_2 -> snk 
            For example:
                {
                    (id1, id2) -> True
                }
                tips: (1, 1) represent a -> a -> snk: And_k2(Or(A_(1, k1, 1, k2)) -> A_(1, k2, 1, len(alphabet)) ) 
    """

    alphabet = None 
    k = None 

    var_list = []
    id_table = {}

    src_to_alphabet1_table = {}
    alphabet1_to_alphabet_table = {}
    alphabet_to_alphabet_table = {}
    alphabet_to_snk_table = {}

    alphabet1_to_alphabet_imply_table = {}
    alphabet_to_alphabet_imply_table = {}
    alphabet_to_snk_imply_table = {}

    formula_deterministic = None

    __number = None
    __size = None

    @classmethod
    def global_init(cls, _alphabet, _k):
        cls.alphabet = _alphabet
        cls.k = _k
        cls.gen_id_table()
        cls.gen_var_list()

    @classmethod
    def gen_id_table(cls):
        """Generate id_table by alphabet."""

        cls.id_table["src"] = 0
        cls.id_table["snk"] = cls.get_size() + 1 
        for idx, ch in enumerate(cls.alphabet, start=1):
            cls.id_table[ch] = idx

    @classmethod 
    def gen_var_list(cls):
        """Generate var_list by alphabet and k."""
        cls.var_list.append(BoolVal(True))
        number = cls.get_number() 
        number = number * number + 1
        for i in range(1, number):
            v_name = "A_{}".format(i)
            cls.var_list.append(Bool(v_name))
        cls.var_list.append(BoolVal(False))

    @classmethod
    def get_number(cls):
        if cls.__number is None:
            cls.__number = cls.k * cls.get_size() + 1

        return cls.__number

    @classmethod
    def get_size(cls):
        if cls.__size is None:
            cls.__size = len(cls.alphabet)

        return cls.__size

    @classmethod
    def gen_deterministic_formula(cls):
        """Generate the formula represent the deterministic property.
        For example: And(Not(And(V6, V7)), ... , Not(And(V23, V24)))
        """

        if cls.k == 1:
            return cls.var_list[0] 

        result = []
        # src -> alphabet
        part_1 = []
        for ch in cls.alphabet:
            # src -> alphabet1 or src -> alphabet1: None
            id2 = cls.id_table[ch]
            var_idx = cls._quadruple_to_idx(0, 0, id2, 1)
            neg_idx_list = [cls._quadruple_to_idx(0, 0, id2, k2) for k2 in range(1, cls.k+1)]
            part_1.append(Or(cls.var_list[var_idx], cls._get_and_formula(neg_idx_list, False)))
        result.extend(part_1)
        # alphabet -> alphabet 
        part_2 = []   
        for ch1 in cls.alphabet:
            for ch2 in cls.alphabet:
                for k1 in range(1, cls.k+1):
                    # ch1 -> ch2: one and only
                    part_2 = []
                    id1 = cls.id_table[ch1]
                    id2 = cls.id_table[ch2]
                    for m in range(1, cls.k+1):
                        pos_idx = cls._quadruple_to_idx(id1, k1, id2, m)
                        neg_idx_list = [cls._quadruple_to_idx(id1, k1, id2, k2) for k2 in range(1, cls.k+1) if k2 != m]
                        part_2.append(And(cls.var_list[pos_idx], 
                            cls._get_and_formula(neg_idx_list, False)))

                    # ch1 -> ch2: none
                    neg_idx_list = [cls._quadruple_to_idx(id1, k1, id2, k2) for k2 in range(1, cls.k+1)] 
                    part_2.append(cls._get_and_formula(neg_idx_list, False))

                    result.append(Or(part_2))

        return And(result)

    @classmethod
    def _get_and_formula(cls, idx_list, ext=True):
        """ Get conjuction of all variables idx in indx_list.
        For example: [1, 2] -> And(V1, V2)

        Args:
            idx_list: [1, 2]
            ext: flag represent positive
        Returns:
            formula: And(V1, V2)
        """
        if len(idx_list) == 0:
            return cls.var_list[0]

        if ext:
            args = [cls.var_list[i] for i in idx_list] 
        else:
            args = [Not(cls.var_list[i]) for i in idx_list] 

        return And(args)

    @classmethod
    def _get_or_formula(cls, idx_list, ext=True):
        """ Get conjuction of all variables idx in indx_list.
        For example: [1, 2] -> And(V1, V2)
        
        Args:
            idx_list: [1, 2]
            ext: flag represent positive
        Returns:
            formula: And(V1, V2)
        """

        if len(idx_list) == 0:
            return cls.var_list[0]

        if ext:
            args = [cls.var_list[i] for i in idx_list] 
        else:
            args = [Not(cls.var_list[i]) for i in idx_list]
        return Or(args)

    @classmethod
    def _get_alphabet_to_alphabet_list(cls, id1, id2, ext=False):
        """Get square list by idx and k.

        Args:
            id1: index in alphabet 
            id2: index in alphabet
            ext: extend flag represent a1->aj
        Returns:
            list: index in var_list
                id1 -> id2 represent all variable list
        """
        result = []
        if ext: 
            # (id1, 1, id2, k2) 
            result = [cls._quadruple_to_idx(id1, 1, id2, k2) for k2 in range(1, cls.k+1)]
        else:
            # (id1, k1, id2, k2)
            if id1 == 0:
                # src -> a1 (0, 0, id2, 1)
                result = [cls._quadruple_to_idx(0, 0, id2, 1)]
            elif id2 == cls.get_size() + 1:
                # a_j -> snk (id1, k1, id2, 0)
                result = [cls._quadruple_to_idx(id1, k1, id2, 0) for k1 in range(1, cls.k+1)]
            else:
                result = [cls._quadruple_to_idx(id1, k1, id2, k2) for k1 in range(1, cls.k+1) for k2 in range(1, cls.k+1)]

        return result

    @classmethod
    def _get_alphabet_to_alphabet_imply_list(cls, id1, id2, id3, ext=False):
        """Get imply list.

        Args:
            id1: pre character index 
            id2: shared character index
            id3: shared character index
            ext: extend flag represent special case 
        Returns:
            list: list of tuple (pre, post) such as ([], [])
        """
        result = []
        if ext:
            # sentence[1] -> sentences[2] -> sentence[3]
            # (id1, 1, id2, k2) -> (id2, k2, id3, k3)
            for k2 in range(1, cls.k+1):
                pre = [cls._quadruple_to_idx(id1, 1, id2, k2)]
                post = [cls._quadruple_to_idx(id2, k2, id3, k3) for k3 in range(1, cls.k+1)]
                result.append((pre, post)) 
        else:
            if id3 == cls.get_size() + 1:
                # sentence[-2] -> sentence[-1] -> snk
                # (id1, k1, id2, k2) -> (id2, k2, snk, 0)
                for k2 in range(1, cls.k+1):
                    if id3 == 3:
                        pre = [cls._quadruple_to_idx(id1, 1, id2, k2)]
                    else:
                        pre = [cls._quadruple_to_idx(id1, k1, id2, k2) for k1 in range(1, cls.k+1)]
                    post = [cls._quadruple_to_idx(id2, k2, id3, 0)]
                    result.append((pre, post))
            else:
                # id1 -> id2 -> id3
                # (id1, k1, id2, k2) -> (id2, k2, id3, k3)
                for k2 in range(1, cls.k+1):
                    pre = [cls._quadruple_to_idx(id1, k1, id2, k2) for k1 in range(1, cls.k+1)]
                    post = [cls._quadruple_to_idx(id2, k2, id3, k3) for k3 in range(1, cls.k+1)]
                    result.append((pre, post))

        # print("{} -> {}".format((id1, id2, id3), result))

        return result

    @classmethod
    def _quadruple_to_idx(cls, id1, k1, id2, k2):
        """Map quadruple into index in var_list.
        For example: (1, 2, 1, 1) -> 11

        Args:
            id1: row character id
            k1: row k-idx
            id2: col character id
            k2: col k-idx

        Returns:
            idx: index in var_list
        """

        size = cls.get_size()
        if id1 == 0 and id2 == size + 1:
            return cls.get_number()

        if id1 == 0:
            return (id2-1) * cls.k + k2

        if id2 == size + 1:
            return ((id1-1) * cls.k + k1 + 1) * cls.get_number()

        return ((id1-1) * cls.k + k1) * cls.get_number() + (id2-1) * cls.k + k2

    @classmethod
    def _idx_to_quadruple(cls, idx):
        """Map quadruple into index in var_list.
        For example: 11 -> (1, 2, 1, 1)

        Args:
            idx: index in var_list
        Returns:
            (id1, k1, id2, k2)
                id1: row character id
                k1: row k-idx
                id2: col character id
                k2: col k-idx
        """

        row, col = divmod(idx, cls.get_number())
        id1, k1 = divmod(row-1, cls.k)
        id2, k2 = divmod(col-1, cls.k)
        return id1+1, k1+1, id2+1, k2+1
    
    @classmethod
    def print_global_table_count(cls):
        count_all = 0
        count_valid = 0
        for key, value in cls.src_to_alphabet1_table.items():
            count_all += value
            count_valid += 1

        for key, value in cls.alphabet1_to_alphabet_table.items():
            count_all += value
            count_valid += 1

        for key, value in cls.alphabet_to_alphabet_table.items():
            count_all += value
            count_valid += 1

        for key, value in cls.alphabet_to_snk_table.items():
            count_all += value
            count_valid += 1

        for key, value in cls.alphabet1_to_alphabet_imply_table.items():
            count_all += value
            count_valid += 1
        
        for key, value in cls.alphabet_to_alphabet_imply_table.items():
            count_all += value
            count_valid += 1

        for key, value in cls.alphabet_to_snk_imply_table.items():
            count_all += value
            count_valid += 1

        print("all: {}, valid: {}".format(count_all, count_valid))

    @classmethod
    def print_global_table(cls):
        print("constraint_a: ")
        print("*" * 100)
        print("src->alphabet: ")
        print(cls.src_to_alphabet1_table)
        print("alphabet1->alphabet: ")
        print(cls.alphabet1_to_alphabet_table)
        print("alphabet->alphabet: ")
        print(cls.alphabet_to_alphabet_table)
        print("alphabet->snk: ")
        print(cls.alphabet_to_snk_table)
        print("*" * 100)
        print("constraint_b: ")
        print("(first)id1->id2->id3: ")
        print(cls.alphabet1_to_alphabet_imply_table)
        print("id1->id2->id3: ")
        print(cls.alphabet_to_alphabet_imply_table)
        print("id1->id2->snk: ")
        print(cls.alphabet_to_snk_imply_table)
        print("*" * 100)

    @classmethod
    def generate_global_constraint(cls):
        """Generate global constraint.

        Returns:
            formula: global constraint formula.
        """
        parts = []
        parts.extend(cls._generate_global_constraint_a())
        parts.extend(cls._generate_global_constraint_b())
        if len(parts) == 0:
            return cls.var_list[0]

        return And(parts)

    @classmethod
    def _generate_global_constraint_a(cls):
        parts = []
        # src -> alphabet
        part_1 = []
        for key, value in cls.src_to_alphabet1_table.items():
            if value>0:
                id2 = key
                part_1.extend(cls._get_alphabet_to_alphabet_list(0, id2))
        parts.append(cls._get_and_formula(part_1))
        # alphabet1 -> alphabet
        part_2 = []
        for key, value in cls.alphabet1_to_alphabet_table.items():
            if value>0:
                id1 = key[0]
                id2 = key[1]
                var_idx_list = cls._get_alphabet_to_alphabet_list(id1, id2, True)
                part_2.append(cls._get_or_formula(var_idx_list))
        parts.extend(part_2)
        # alphabet -> aphabet
        part_3 = []
        for key, value in cls.alphabet_to_alphabet_table.items():
            if value>0:
                id1 = key[0]
                id2 = key[1]
                var_idx_list = cls._get_alphabet_to_alphabet_list(id1, id2)
                part_3.append(cls._get_or_formula(var_idx_list))
        parts.extend(part_3)
        # alphabet -> snk
        part_4 = []
        for key, value in cls.alphabet_to_snk_table.items():
            if value>0:
                id1 = key
                var_idx_list = cls._get_alphabet_to_alphabet_list(id1, cls.get_size()+1)
                part_4.append(cls._get_or_formula(var_idx_list))
        parts.extend(part_4)

        return parts
 
    @classmethod
    def _generate_global_constraint_b(cls):
        parts = []
        # alphabet1 -> alphabet2 -> alphabet3
        part_1 = []
        for key, value in cls.alphabet1_to_alphabet_imply_table.items():
            if value>0:
                id1 = key[0]
                id2 = key[1]
                id3 = key[2]
                pre_post_list = cls._get_alphabet_to_alphabet_imply_list(id1, id2, id3, True)
                for pre_post in pre_post_list:
                    part_1.append(Implies(cls._get_or_formula(pre_post[0]), 
                        cls._get_or_formula(pre_post[1]))) 
        parts.extend(part_1)
        # id1 -> id2 -> id3
        part_2 = []
        for key, value in cls.alphabet_to_alphabet_imply_table.items():
            if value>0:
                id1 = key[0]
                id2 = key[1]
                id3 = key[2]
                pre_post_list = cls._get_alphabet_to_alphabet_imply_list(id1, id2, id3)
                for pre_post in pre_post_list:
                    part_2.append(Implies(cls._get_or_formula(pre_post[0]), 
                        cls._get_or_formula(pre_post[1]))) 
        parts.extend(part_2)
        # id1 -> id2 -> snk
        part_3 = []
        for key, value in cls.alphabet_to_snk_imply_table.items():
            if value>0:
                id1 = key[0]
                id2 = key[1]
                pre_post_list = cls._get_alphabet_to_alphabet_imply_list(id1, id2, cls.get_size()+1)
                for pre_post in pre_post_list:
                    part_3.append(Implies(cls._get_or_formula(pre_post[0]), 
                        cls._get_or_formula(pre_post[1])))
        parts.extend(part_3)
        return parts

    def __init__(self, sentence):
        self.sentence = sentence

    def gen_sentence_constraint(self, ext=True):
        """Generate formula representing the constraint.
       
        Args:
            ext: flag represent whether return formula
        Returns:
            formula: the constraint
        """

        slen = len(self.sentence)
        if slen == 0:
            const_a = SentenceTranslator.var_list[0] # true
        else:
            const_a = self._gen_sentence_constraint_a(ext)

        if SentenceTranslator.k <= 1:
            const_b = SentenceTranslator.var_list[0] # True
        else:
            const_b = self._gen_sentence_constraint_b(ext)

        if ext:
            result = And(const_a, const_b)
            return result 

    def _gen_sentence_constraint_a(self, ext=True):
        """Generate the first part of sentence constraint.
        Args:
            ext: flag represent whether return formula
        Returns:
            formula: the first part constraint if ext is True
        """
        if ext:
            return self.__gen_constraint_a_formula()

        # update global alphabet to alphabet table

        # src -> id2
        id2 = SentenceTranslator.id_table[self.sentence[0]]
        # SentenceTranslator.src_to_alphabet1_table[id2] = True
        count = SentenceTranslator.src_to_alphabet1_table.setdefault(id2, 0) 
        SentenceTranslator.src_to_alphabet1_table[id2] += 1
        # id1 -> snk
        id1 = SentenceTranslator.id_table[self.sentence[-1]]
        # SentenceTranslator.alphabet_to_snk_table[id1] = True
        count = SentenceTranslator.alphabet_to_snk_table.setdefault(id1, 0)
        SentenceTranslator.alphabet_to_snk_table[id1] += 1

        slen = len(self.sentence)
        if slen > 1:
            # id1 -> id2
            id1 = SentenceTranslator.id_table[self.sentence[0]]
            id2 = SentenceTranslator.id_table[self.sentence[1]]
            # SentenceTranslator.alphabet1_to_alphabet_table[(id1, id2)] = True
            count = SentenceTranslator.alphabet1_to_alphabet_table.setdefault((id1, id2), 0)
            SentenceTranslator.alphabet1_to_alphabet_table[(id1, id2)] += 1

        if slen > 2:
            for i in range(1, slen-1):
                id1 = SentenceTranslator.id_table[self.sentence[i]]
                id2 = SentenceTranslator.id_table[self.sentence[i+1]]
                # SentenceTranslator.alphabet_to_alphabet_table[(id1, id2)] = True
                count = SentenceTranslator.alphabet_to_alphabet_table.setdefault((id1, id2), 0)
                SentenceTranslator.alphabet_to_alphabet_table[(id1, id2)] += 1

    def _gen_sentence_constraint_b(self, ext=True):
        """Generate the second part of sentence constraint.
        
        Args:
            ext: flag represent whether return formula
        Returns:
            formula: the second part constraint if ext is True
        """
        if ext:
            return self.__gen_constraint_b_formula()

        # update global alphabet to alphabet imply table
        slen = len(self.sentence)
        if slen > 1:
            id1 = SentenceTranslator.id_table[self.sentence[-2]]
            id2 = SentenceTranslator.id_table[self.sentence[-1]]
            # SentenceTranslator.alphabet_to_snk_imply_table[(id1, id2)] = True
            count = SentenceTranslator.alphabet_to_snk_imply_table.setdefault((id1, id2), 0)
            SentenceTranslator.alphabet_to_snk_imply_table[(id1, id2)] += 1 

        if slen > 2:
            id1 = SentenceTranslator.id_table[self.sentence[0]]
            id2 = SentenceTranslator.id_table[self.sentence[1]]
            id3 = SentenceTranslator.id_table[self.sentence[2]]
            # SentenceTranslator.alphabet1_to_alphabet_imply_table[(id1, id2, id3)] = True
            count = SentenceTranslator.alphabet1_to_alphabet_imply_table.setdefault((id1, id2, id3), 0)
            SentenceTranslator.alphabet1_to_alphabet_imply_table[(id1, id2, id3)] += 1 
            for i in range(1, slen-2):
                id1 = SentenceTranslator.id_table[self.sentence[i]]
                id2 = SentenceTranslator.id_table[self.sentence[i+1]]
                id3 = SentenceTranslator.id_table[self.sentence[i+2]]
                # SentenceTranslator.alphabet_to_alphabet_imply_table[(id1, id2, id3)] = True
                count = SentenceTranslator.alphabet_to_alphabet_imply_table.setdefault((id1, id2, id3), 0)
                SentenceTranslator.alphabet_to_alphabet_imply_table[(id1, id2, id3)] += 1 
    
    def __gen_constraint_a_formula(self):
        slen = len(self.sentence)
        parts = []
        parts.append(self.__gen_a_src())
        if slen > 1:
            parts.append(self.__gen_a_src_1())
        if slen > 2:
            parts.append(self.__gen_a_common())
        parts.append(self.__gen_a_snk())
        result = And(parts)
        return result

    def __gen_a_src(self):
        id2 = SentenceTranslator.id_table[self.sentence[0]]
        idx = SentenceTranslator._quadruple_to_idx(0, 0, id2, 1)
        return SentenceTranslator.var_list[idx]

    def __gen_a_src_1(self):
        id1 = SentenceTranslator.id_table[self.sentence[0]]
        id2 = SentenceTranslator.id_table[self.sentence[1]]
        idx_list = [SentenceTranslator._quadruple_to_idx(id1, 1, id2, j) for j in range(1, SentenceTranslator.k +1)]

        return SentenceTranslator._get_or_formula(idx_list)

    def __gen_a_common(self):
        result = []
        for i in range(1, len(self.sentence)-1):
            id1 = SentenceTranslator.id_table[self.sentence[i]]
            id2 = SentenceTranslator.id_table[self.sentence[i+1]]
            start_idx = SentenceTranslator._quadruple_to_idx(id1, 1, id2, 1)
            square_list = SentenceTranslator._get_alphabet_to_alphabet_list(id1, id2)
            result.append(SentenceTranslator._get_or_formula(square_list))

        return And(result)

    def __gen_a_snk(self):
        id1 = SentenceTranslator.id_table[self.sentence[-1]]
        slen = len(self.sentence)
        size = len(SentenceTranslator.alphabet)

        if slen == 1:
            idx = SentenceTranslator._quadruple_to_idx(id1, 1, size+1, 0)
            return SentenceTranslator.var_list[idx]
        idx_list = [SentenceTranslator._quadruple_to_idx(id1, k1, size+1, 0) for k1 in range(1, SentenceTranslator.k+1)] 
        return SentenceTranslator._get_or_formula(idx_list)

    def __gen_constraint_b_formula(self):        
        slen = len(self.sentence)
        if slen <= 1:
            return SentenceTranslator.var_list[0] # True
        
        parts = []
        if slen > 2:
            parts.append(self.__gen_b_src())
            parts.append(self.__gen_b_common())
        if slen > 1:
            parts.append(self.__gen_b_snk())

        return And(parts) 

    def __gen_b_src(self):
        id1 = SentenceTranslator.id_table[self.sentence[0]]
        id2 = SentenceTranslator.id_table[self.sentence[1]]
        id3 = SentenceTranslator.id_table[self.sentence[2]]

        result = []
        for j in range(1, SentenceTranslator.k + 1):
            pre_idx = SentenceTranslator._quadruple_to_idx(id1, 1, id2, j)
            pre = SentenceTranslator.var_list[pre_idx]
            post_idx_list = [SentenceTranslator._quadruple_to_idx(id2, j, id3, j1) for j1 in range(1, SentenceTranslator.k + 1)]
            post = SentenceTranslator._get_or_formula(post_idx_list)
            result.append(Implies(pre, post))
        
        return And(result) 

    def __gen_b_common(self):
        result = []
        for i in range(1, len(self.sentence)-2):
            id1 = SentenceTranslator.id_table[self.sentence[i]]
            id2 = SentenceTranslator.id_table[self.sentence[i+1]]
            id3 = SentenceTranslator.id_table[self.sentence[i+2]]

            pre_post_list = SentenceTranslator._get_alphabet_to_alphabet_imply_list(id1, id2, id3)
            for pre_post in pre_post_list:
                pre = SentenceTranslator._get_or_formula(pre_post[0])
                post = SentenceTranslator._get_or_formula(pre_post[1])
                result.append(Implies(pre, post))

        if len(result) == 0:
            return SentenceTranslator.var_list[0]

        return And(result)

    def __gen_b_snk(self):
        id1 = SentenceTranslator.id_table[self.sentence[-2]]
        id2 = SentenceTranslator.id_table[self.sentence[-1]]

        size = len(SentenceTranslator.alphabet)
        slen = len(self.sentence)

        result = []

        for j in range(1, SentenceTranslator.k + 1):
            if slen == 2:
                pre_idx = SentenceTranslator._quadruple_to_idx(id1, 1, id2, j)
                pre = SentenceTranslator.var_list[pre_idx] 
            else:
                pre_id_list = [SentenceTranslator._quadruple_to_idx(id1, j1, id2, j) for j1 in range(1, SentenceTranslator.k + 1)]
                pre = SentenceTranslator._get_or_formula(pre_id_list)
            post_idx = SentenceTranslator._quadruple_to_idx(id2, j, size+1, 0)
            post = SentenceTranslator.var_list[post_idx]
            result.append(Implies(pre, post))
    
        return And(result)


def test():
    # test id_table
    SentenceTranslator.gen_id_table()
    print(SentenceTranslator.id_table)
    # test var_list
    SentenceTranslator.gen_var_list()
    # test square_list
    square = SentenceTranslator._get_square_list(6)
    print(square)
    # test _quadruple_to_idx
    idx = SentenceTranslator._quadruple_to_idx(1, 2, 1, 1)
    quadruple = SentenceTranslator._idx_to_quadruple(11)
    print("{} <=> {}".format(idx, quadruple))

    idx = SentenceTranslator._quadruple_to_idx(2, 2, 2, 2)
    quadruple = SentenceTranslator._idx_to_quadruple(24)
    print("{} <=> {}".format(idx, quadruple))

    idx = SentenceTranslator._quadruple_to_idx(1, 1, 1, 1)
    quadruple = SentenceTranslator._idx_to_quadruple(6)
    print("{} <=> {}".format(idx, quadruple))

    kid = SentenceTranslator._quadruple_to_kid(1, 1, 2, 2)
    quadruple = SentenceTranslator._kid_to_quadruple(4)
    print("{} <=> {}".format(kid, quadruple))

    print(SentenceTranslator._get_imply_list(1, 1, 2, 2))

    print(SentenceTranslator.gen_deterministic_formula())

 

def run():
    SentenceTranslator.gen_id_table()
    SentenceTranslator.gen_var_list()
    print(SentenceTranslator.gen_deterministic_formula())
    sentences = ["", "a", "ab", "abbb", "aabb"]
    for sen in sentences:
        s = SentenceTranslator(sen)
        print(s.gen_sentence_constraint())



if __name__ == "__main__":
    run()

