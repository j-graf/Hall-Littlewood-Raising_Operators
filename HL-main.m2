--

restart
largestIndex = 30 --at most ~30
F1 = QQ[t]
R1 = F1[q_(-largestIndex)..q_(largestIndex)]/(ideal(join({q_0-1},for k from -largestIndex to -1 list q_k)))
S1 = F1[b_(-largestIndex)..b_(largestIndex)]/(ideal(join({b_0-1},for k from -largestIndex to -1 list b_k)))

protect symbol q
protect symbol b
protect symbol F
protect symbol R1
protect symbol S1
protect symbol largestIndex

---------- conversions between p_i's and q_i's

qTObList = {1}
for n from 1 to largestIndex do (
    qTObList = append(qTObList,- sum for i from 1 to n list((-1)^i*b_i*qTObList#(n-i)))
    )
qTObList = Bag qTObList

bTOqList = {1}
for n from 1 to largestIndex do (
    bTOqList = append(bTOqList,- sum for i from 1 to n list((-1)^i*q_i*bTOqList#(n-i)))
    )
bTOqList = Bag bTOqList

--maps q_i -> b_j's
qTObMap = map(ring b_1,ring q_1,toList(largestIndex:0)|toList(qTObList));

--maps b_i -> q_j's
bTOqMap = map(ring q_1,ring b_1,toList(largestIndex:0)|toList(bTOqList));

--maps any f -> q_i's
TOq = f -> (
    if (ring f) === (ring q_1) then return(f);
    if (ring f) === ZZ or (ring f) === QQ or (ring f) === (ring (5*t)) or (ring f) === (ring (t/2)) then return(sub(f,ring q_1));
    bTOqMap f
    )

--maps any f -> b_i's
TOb = f -> (
    if (ring f) === (ring b_1) then return(f);
    if (ring f) === ZZ or (ring f) === QQ or (ring f) === (ring (5*t)) or (ring f) === (ring (t/2)) then return(sub(f,ring b_1));
    qTObMap f
    )

---------- compute Q_lambda and B_lambda

qlam = lam -> (
    product for thePart in lam list q_(thePart)
    )

blam = lam -> (
    product for thePart in lam list b_(thePart)
    )

tailSum = (lam,ind) -> (
    sum lam_{ind..(#lam-1)}
    )

raisingOpQ = lam -> (
    product flatten for i from 1 to #lam list (
        for j from i+1 to #lam+1 list (
            1 + sum for k from 1 to tailSum(lam,j-1) list ((1+0*(t^k-t^(k-1)))*R_(i,j)^k)
            )
        )
    )

Qtwo = (r,s) -> (
    q_r*q_s + (t-1) * (sum for i from 1 to s list ((t)^(i-1)*q_(r+i)*q_(s-i)))
    )

Btwo = (r,s) -> (
    b_r*b_s + (1-t) * (sum for i from 1 to s list ((-1)^r*b_(r+i)*b_(s-i)))
    )

-- computes R_ij(lam), where i,j start at 0
Rij = (i,j,lam) -> (
    Rijn(i,j,1,lam)
    )

-- computes R_ij^n(lam), where i,j start at 0
Rijn = (i,j,n,lam) -> (
    if i > j or i < 0 or j < 0 or i >= #lam or j >= #lam then (
        error "Rijn: index out of range";
        );
    if i == j then return lam;
    
    lam + (toList(i:0)|{n}|toList((j-i-1):0)|{-n}|toList((#lam-j-1):0))
    )

Q = lam -> (
    ansList := {(lam,1)};
    
    for jAnti from 0 to #lam-1 do (
        j := #lam-jAnti-1;
        for iAnti from jAnti+1 to #lam-1 do (
            i := #lam-iAnti-1;
            
            for theTerm in ansList do (
                for n from 1 to tailSum(theTerm#0,j) do (
                    ansList = append(ansList,(Rijn(i,j,n,theTerm#0),(theTerm#1)*(t^n-t^(n-1))));
                    );
                );
            );
        );
    
    sum for theTerm in ansList list ((theTerm#1)*qlam(theTerm#0))
    )
