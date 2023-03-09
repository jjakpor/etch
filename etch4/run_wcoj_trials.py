import sqlite3
import random
from scipy.sparse import csr_matrix
import scipy.sparse
import numpy as np
from matplotlib import pyplot as plt
import subprocess

def commit(c, r, s, t):
    c.execute('delete from r')
    c.executemany(f'INSERT INTO r VALUES(?,?)', r)
    c.execute('delete from s')
    c.executemany(f'INSERT INTO s VALUES(?,?)', s)
    c.execute('delete from t')
    c.executemany(f'INSERT INTO t VALUES(?,?)', t)
    c.commit()

# for a description of this join problem see https://arxiv.org/pdf/1310.3314.pdf, Figure 2
def go_(con, n):
    def edges(n, r):
        for A in range(n):
            r.add((1, A))
            r.add((A, 1))

    r = set()
    s = set()
    t = set()
    edges(n, r)
    edges(n, s)
    edges(n, t)
    commit(con, r, s, t)

def fig(scales, sql, se, etch):
    def norm(arr):
        return np.array(arr)/arr[-1]
    plt.plot(scales, norm(sql), label='sqlite')
    plt.plot(se, norm(etch)*2, label='etch')
    plt.plot(se, norm(np.array(se**(1.0)))*2, label='n^1')
    plt.plot(scales, norm(np.array(scales**2)), label='n^2')
    plt.xscale('log')
    plt.yscale('log')
    plt.legend()
    plt.savefig('wcoj_scaling.pdf')

def parse_stdout(b):
    return [int(x) for x in b.decode().strip().split('\n')]
    #return int(b.decode())
def main():
    global con
    con = sqlite3.connect("./data/pldi.db")
    print("\n\n\n/*** START TEST ***/\n")
    print("   this tests ETCH's scaling for the triangle query.\n");
    print("   cf: Figure 14: Worst-case optimal join\n");
    #for sn in [10, 20]:
    results = []
    #scales = [10,20,30,40,50,60,70,80,90,100]
    scales = np.array([70,80,90,100,110,120 ,130,140,150,160,170,180])*8
    #scales = s
    for sn in scales:
        print(sn, ":")
        go_(con, sn)
        #print(list(con.execute('select count(*) from r')))
        pair = parse_stdout(subprocess.check_output('./wcoj'))
        results.append(pair)
    return (scales, results)

def foo():
    result = subprocess.check_output(["echo", "22"])
    print(int(result))

(s, r) = main()

sql = [p[0] for p in r]
etch = [p[1] for p in r]

fig(s, sql, s, etch)