#!/usr/bin/python
from __future__ import division
import sys
import os
import numpy as np
from sympy import *
def left_n(n,N):
    temp=np.zeros([N,1])
    temp[n][0]=1
    return temp
def right_n(n,N):
    temp=np.zeros([1,N])
    temp[0][n]=1
    return temp
def tenser_p(N,n,m,a):
    global record
    index=record.keys()
    index.sort()
    index.remove(index[0])
    if n==0:
        temp1=left_n(a,record[n]).dot(right_n(0,record[n]))
        temp2=left_n(0,record[n]).dot(right_n(a,record[n]))
    else:
        temp1=np.eye(record[0])
        temp2=np.eye(record[0])
    for i in index:
        if i!=n:
            temp1=np.kron(temp1,np.eye(record[i]))
            temp2=np.kron(temp2,np.eye(record[i]))
        else:
            temp1=np.kron(temp1,left_n(a,record[n]).dot(right_n(0,record[n])))
            temp2=np.kron(temp2,left_n(0,record[n]).dot(right_n(a,record[n])))
    ot=temp1.dot(m).dot(temp2) 
    return ot
def matsum(n,m):
    global record
    dim=record[n]
    temp=tenser_p(dim,n,m,0)
    for i in range(1,dim):
        temp+=tenser_p(dim,n,m,i)
    return temp
def adjoint(m):
    return m.T
def pow(m,n):
    temp=m
    for i in range(n-1):
        temp=temp.dot(temp)
    return temp
def Split(n):
    a=str(n)
    b=[int(item) for item in a]
    b.sort()
    return b
def matUtrans(U,n,m):
    global record
    index=record.keys()
    index.sort()
    index.remove(index[0])
    n=Split(n)
    flag=0
    if n[0]==0:
        temp=adjoint(U)
        flag=1
    else:
        temp=np.eye(record[0])
    for i in index:
        if i not in n:
            temp=np.kron(temp,np.eye(record[i]))
        elif flag==0:
            temp=np.kron(temp,adjoint(U))
            flag=1
    ot=temp.dot(m).dot(adjoint(temp))
    return ot
def matUtransC(C_U,n,m):
    global record
    A0=np.array([[1,0],[0,0]])
    A1=np.array([[0,0],[0,1]])
    index=record.keys()
    index.sort()
    index.remove(index[0])
    n=Split(n)
    if n[0]==0:
        temp0=A0
        temp1=A1
    else:
        temp0=np.eye(record[0])
        temp1=np.eye(record[0])
    for i in index:
        if i==n[0]:
            temp0=np.kron(temp0,A0)
            temp1=np.kron(temp1,A1)
        elif i==n[1]:
            temp0=np.kron(temp0,np.eye(record[i]))
            temp1=np.kron(temp1,adjoint(C_U))
        else:
            temp0=np.kron(temp0,np.eye(record[i]))
            temp1=np.kron(temp1,np.eye(record[i]))
    temp=temp0+temp1
    ot=temp.dot(m).dot(adjoint(temp))
    return ot
def fixpoint(m0,m1,q,p):
    return (m0.T).dot(p).dot(m0)+(m1.T).dot(Q).dot(m1)
def order(m1,m2):
	flag=0
        #print(m1)
	m=m1-m2
        m=m.astype(complex)
	eigvalue=np.linalg.eigvals(m)
        #print(eigvalue)
	for i in eigvalue:
		if i<-10**(-15):
                    print i
		    flag=1
	return flag
term=sys.argv[1]
#term='order#matsum#0,matsum#1,matsum#2,matsum#3,matUtrans#Delta,2,matUtrans#H,0,matUtrans#H,1,matUtrans#H,2,fixpoint#M0,M1,Q,#adjoint#N0@.dot#P@.dot#N0@+#adjoint#N1@.dot#P@.dot#N1@+#adjoint#N2@.dot#P@.dot#N2@+#adjoint#N3@.dot#P@.dot#N3@+mat0@@@@@@@@@@@@@,I@'
#term='order#matUtrans#Or,10,matUtrans#H,0,matUtrans#H,1,matUtrans#Ph,10,matUtrans#H,0,matUtrans#H,1,G@@@@@@,Q@'
#term='order(matsum(0,matUtrans(H,0,matUtrans(C_U,10,matUtrans(adjoint(C_U),10,matUtrans(adjoint(H),0,(adjoint(M0).dot(Q).dot(M0)+(adjoint(M1).dot(Q).dot(M1)))))))),P)'
record={}
path=os.path.join(os.path.abspath(os.curdir),'param.txt')
execfile(path)
for i in range(len(var_type)):
    record[i]=var_type[i]
term=term.replace('+mat0','')
term=term.replace('#','(')
term=term.replace('@',')')
term=term.replace('s(C_U','sC(C_U')
term=term.replace('(adjoint(C_U','C(adjoint(C_U')
#extract_record(term)
result=eval(term)
print result==0

