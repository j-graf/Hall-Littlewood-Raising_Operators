# Hall-Littlewood-Raising_Operators
Computes Hall-Littlewood functions with raising operators

# Examples

## Hall-Littlewood Computations

1. Verify $Q_\lambda(A;0)=B_{\lambda'}(A;0)$, where $\lambda=(4,2,1)$:
```
lam = {4,2,1}
sub(Q lam,t=>0) == sub(B conj lam,t=>0)
sub(B lam,t=>0) == sub(Q conj lam,t=>0)
```
