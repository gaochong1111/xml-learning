from TS import SentenceTranslator as ST
from z3 import BoolVal, And, Not, Solver
from sys import argv, exit
import time


def read_file(path="demo_test.txt"):
    result = [] # need no repeat
    alphabet = set()
    with open(path) as fin: 
        for idx, line in enumerate(fin):
            line = line.replace("\n", "").replace("\r", "")
            tmp = line.split(",")
            result.append(tmp)

            for ch in tmp:
                alphabet.add(ch)
    return result, alphabet 


def init_st():
    ST.global_init(["a", "b", "c", "d", "e"], 7)
    # ST.global_init(["a", "b" , "c"], 1)

def get_pos_and_neg_from_file(pos_path, neg_path):
    sen_pos, alphabet1 = read_file(pos_path)
    sen_neg, alphabet2  = read_file(neg_path)
    alphabet = alphabet1 & alphabet2

    return sen_pos, sen_neg, sorted(list(alphabet))


def get_pos_from_file(file_path):
    sen_pos, alphabet = read_file(file_path)
    return sen_pos, sorted(list(alphabet))


def generate_fomula(sen_pos, sen_neg):
    # deterministic formula
    d_formula = ST.gen_deterministic_formula()
    # postive sentences -> constraint
    for s in sen_pos:
        st = ST(s)
        st.gen_sentence_constraint(False)
    
    ST.print_global_table_count()

    formula_pos = ST.generate_global_constraint()
    # negative sentences -> constraint 
    formula_neg_list = [BoolVal(True)]
    for s in sen_neg:
        st = ST(s)
        st_const = st.gen_sentence_constraint()
        formula_neg_list.append(Not(st_const))
    formula_neg = And(formula_neg_list)
    # all constraint
    formula = And(d_formula, formula_pos, formula_neg)
    return formula


def solve(formula):
    solver = Solver()
    solver.add(formula)
    # print(formula)
    result = solver.check()
    if str(result) == "sat":
        m = solver.model()
        if len(ST.alphabet) < 3 and ST.k < 3:
            for v in ST.var_list:
                print("{}: {}".format(v, m[v]))
    elif str(result) == "unsat":
            print("UNSAT")
        
def step1(pos_path, neg_path):
    start = time.time()
    if neg_path is None:
        sen_pos, alphabet = get_pos_from_file(pos_path)
        sen_neg = []
    else:
        sen_pos, sen_neg, alphabet = get_pos_and_neg_from_file(pos_path, neg_path)
    end = time.time()


    print("step1 READING: alphabet={}, pos_sentences={}, neg_sentences={}, time cost: {:.4f}".format(len(alphabet), len(sen_pos), len(sen_neg), (end-start)))
    return sen_pos, sen_neg, alphabet

def step2(sen_pos, sen_neg, alphabet, k):
    start = time.time()
    ST.global_init(alphabet, k)
    formula = generate_fomula(sen_pos, sen_neg)
    end = time.time()

    print("step2 TRANSLATING: alphabet={}, pos_sentences={}, neg_sentences={}, time cost: {:.4f}".format(len(alphabet), len(sen_pos), len(sen_neg), (end-start)))

    return formula


def step3(formula):
    start = time.time()
    solve(formula)
    end = time.time()
    print("step3 SOLVING: k={}, alphabet={}, time cost: {:.4f}s".format(ST.k, len(ST.alphabet), (end-start)))


def parse_argv():
    argc = len(argv)
    if argc <= 2 or argc >= 5:
        print("Usage: python ts_demo.py pos_path, k")
        print(" or python ts_demo.py pos_path, neg_path, k")
        exit(0)

    pos_path = argv[1]
    neg_path = None
    if len(argv) == 4:
        neg_path = argv[2]

    k = int(argv[-1])
    return pos_path, neg_path, k


def run():
    # parse 
    pos_path, neg_path, k = parse_argv()
    # read 
    sen_pos, sen_neg, alphabet = step1(pos_path, neg_path)
    # trans (the bottleneck)
    formula = step2(sen_pos, sen_neg, alphabet, k)
    if len(ST.alphabet) < 3 and ST.k < 3:
        print(formula)
    # solve
    step3(formula)

if __name__ == "__main__":
    run()
    # test_read_file()
