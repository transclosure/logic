;def bsearch(A, x):
;    ans = -1
;    l = 0
;    r = len(A) - 1
;    while l <= r and ans == -1:
;        m = (l + r) / 2
;        if A[m] == x:
;            ans = m
;        elif A[m] < x:
;            l = m + 1
;        elif A[m] > x:
;            r = m - 1
;    return ans
