#!/usr/bin/python
import sys
import numpy as np
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
        temp1=left_n(a,record[n])*right_n(0,record[n])
        temp2=left_n(0,record[n])*right_n(a,record[n])
    else:
        temp1=np.eye(record[0])
        temp2=np.eye(record[0])
    for i in index:
        if i!=n:
            temp1=np.kron(temp1,np.eye(record[i]))
            temp2=np.kron(temp2,np.eye(record[i]))
        else:
            temp1=np.kron(temp1,left_n(a,record[n])*right_n(0,record[n]))
            temp2=np.kron(temp2,left_n(0,record[n])*right_n(a,record[n]))
    ot=temp1*m*temp2 
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
    return m**n
def matUtrans(U,n,m):
    global record
    index=record.keys()
    index.sort()
    index.remove(index[0])
    if n==0:
        temp=adjoint(U)
    else:
        temp=np.eye(record[0])
    for i in index:
        if i!=n:
            temp=np.kron(temp,np.eye(record[i]))
        else:
            temp=np.kron(temp,adjoint(U))
    ot=temp*m*adjoint(temp)
    return ot
def order(m1,m2):
	flag=0
	m=m2-m1
	eigvalue=np.linalg.eigvals(m)
	for i in eigvalue:
		if i<0:
			flag=1
	return flag

term=sys.argv[1]
#term='order(matsum(0,matsum(1,matsum(2,matsum(3,matUtrans(Delta,2,matUtrans(H,0,matUtrans(H,1,matUtrans(H,2,(adjoint(M0)*(adjoint(N0)*P*N0+(adjoint(N1)*P*N1+(adjoint(N2)*P*N2+(adjoint(N3)*P*N3+mat0))))*M0+adjoint(M1)*Q*M1))))))))),I)'
#term='order#matsum#0,matsum#1,matUtrans#H,1,matUtrans#R2,2,matUtrans#U,2,matUtrans#H,1,matUtrans#pow#U,2@,2,matUtrans#adjoint#pow#U,2@@,2,matUtrans#adjoint#H@,1,matUtrans#adjoint#U@,2,matUtrans#adjoint#R2@,0,matUtrans#adjoint#H@,0,#adjoint#M0@*Q*M0+#adjoint#M1@*Q*M1+#adjoint#M2@*Q*M2+#adjoint#M3@*Q*M3+mat0@@@@@@@@@@@@@@@@,P@'
record={}
execfile('param1.txt')
for i in range(len(var_type)):
    record[i]=var_type[i]
term=term.replace('+mat0','')
term=term.replace('#','(')
term=term.replace('@',')')
#extract_record(term)
result=eval(term)
print result==0
