# Syntax:
# ("Var", n) dBI
# ("Bind", expr)
# ("Lam", expr, expr)
# ("Pi", expr, expr)
# ("Const", str)
# ("App", expr, expr)

# Context = tuple of types

AXIOM = {"*": "□"}  # This forbids multi-sorted PTS's.
PRODUCT = {("*", "*"): "*", ("□", "*"): "*"}
ROLL_LOG = False
def print_log(*a, **kwa):
    if ROLL_LOG:
        print(*a, **kwa)

def new_name(names, old_names):
    # it doesn't think of many good names!
    i = 0
    while True:
        for n in names:
            if i != 0:
                n = n + "_" + str(i)
            if n not in old_names:
                return n
        i += 1

def pretty_name(expr, names=()):
    if expr[0] == "Var":
        return names[expr[1]]
    elif expr[0] == "Bind":
        raise ValueError("Not a well-formed expression.")
    elif expr[0] == "Lam":
        v = new_name("xyzwuvabcmn", names)
        return "(λ" + v + ":" +\
            pretty_name(expr[1], names) + " -> " + \
            pretty_name(expr[2][1], (v,) + names) + ")"
    elif expr[0] == "Pi":
        v = new_name("ABCMNUVWXYZ", names)
        return "([" + v + ":" +\
               pretty_name(expr[1], names) + "] " +\
               pretty_name(expr[2][1], (v,) + names) + ")"
    elif expr[0] == "Const":
        return expr[1]
    elif expr[0] == "App":
        return "(" + pretty_name(expr[1], names) + " " + pretty_name(expr[2], names) + ")"
    else:
        raise ValueError(expr)

def _pretty_ctxt(ctxt, names=()):
    "Returns names for ctxt variables, and their pretty types."
    if len(ctxt) == 0:
        return (), names
    names, types = _pretty_ctxt(ctxt[1:], names)
    v = new_name("xyzwuvabcmn", names)
    return (v,) + names, (pretty_name(ctxt[0], names),) + types

def pretty_ctxt(ctxt):
    names, types = _pretty_ctxt(ctxt)
    return names, "; ".join(names[i] + ":" + types[i] for i in range(len(ctxt)-1, -1, -1))

def pretty(expr):
    if expr[0] == "Var":
        return str(expr[1])
    elif expr[0] == "Bind":
        return "." + pretty(expr[1])
    elif expr[0] == "Lam":
        return "(λ" + pretty(expr[1]) + pretty(expr[2]) + ")"
    elif expr[0] == "Pi":
        return "(Π" + pretty(expr[1]) + pretty(expr[2]) + ")"
    elif expr[0] == "Const":
        return expr[1]
    elif expr[0] == "App":
        return "(" + pretty(expr[1]) + " " + pretty(expr[2]) + ")"
    else:
        raise ValueError(expr)

def lift(expr, n=1, k=0):
    """Lift all the variables greater or equal to k up n levels."""
    if expr[0] == "Var":
        if expr[1] >= k:
            return ("Var", expr[1] + n)
        else:
            return expr
    elif expr[0] == "Bind":
        return ("Bind", lift(expr[1], n, k+1))
    elif expr[0] == "Lam":
        return ("Lam", lift(expr[1], n, k), lift(expr[2], n, k))
    elif expr[0] == "Pi":
        return ("Pi", lift(expr[1], n, k), lift(expr[2], n, k))
    elif expr[0] == "Const":
        return expr
    elif expr[0] == "App":
        return ("App", lift(expr[1], n, k), lift(expr[2], n, k))
    else:
        raise ValueError(expr)

def subst(expr, s, k=0):
    "Substitute (Var 0) for s in expr, and lowering the indices."
    # (\. -> 0 1)[1 2] --> (\. -> 0 [2 3])
    if expr[0] == "Var":
        if expr[1] == k:
            return s
        elif expr[1] > k:
            return ("Var", expr[1] - 1)
        else:
            return expr
    elif expr[0] == "Bind":
        return ("Bind", subst(
            expr[1],
            lift(s),
            k+1))
    elif expr[0] == "Lam":
        return ("Lam", subst(expr[1], s, k), subst(expr[2], s, k))
    elif expr[0] == "Pi":
        return ("Pi", subst(expr[1], s, k), subst(expr[2], s, k))
    elif expr[0] == "Const":
        return expr
    elif expr[0] == "App":
        return ("App", subst(expr[1], s, k), subst(expr[2], s, k))
    else:
        raise ValueError(expr)

def Var(n):
    return ("Var", n)
def Lam(t, m):
    return ("Lam", t, ("Bind", m))
def Pi(t, m):
    return ("Pi", t, ("Bind", m))
def App(n, m):
    return ("App", n, m)
def Const(s):
    return ("Const", s)

def whnf(expr):
    # print("WHNF:", pretty(expr))
    if expr[0] == "Var":
        return expr
    elif expr[0] == "Bind":
        return expr
    elif expr[0] == "Lam":
        return expr
    elif expr[0] == "Pi":
        return expr
    elif expr[0] == "Const":
        return expr
    elif expr[0] == "App":
        e = whnf(expr[1])
        if e[0] == "Lam":
            # expr == (App e=(Lam t (Bind m)) n)
            return whnf(subst(e[2][1], expr[2]))  # this doesn't necessarily terminate
        return App(e, expr[2])
    else:
        raise ValueError(expr)

def wff(expr):
    pass

def type_infer(expr, ctxt=()):
    # TODO: trace it
    nm, c = pretty_ctxt(ctxt)
    print_log("Infer:", c, "|-", pretty_name(expr, nm), ": ?")
    if expr[0] == "Var":
        if len(ctxt) <= expr[1]:
            raise ValueError("Variable out of context scope.")
        return lift(ctxt[expr[1]], expr[1]+1)
    elif expr[0] == "Bind":
        raise ValueError("Not a well-formed expression.")
    elif expr[0] == "Lam":
        (_, t, (_, m)) = expr # (Lam t (Bind m))
        mt = type_infer(m, (t,) + ctxt)
        srt = type_infer(Pi(t, mt), ctxt)
        return Pi(t, mt)
    elif expr[0] == "Pi":
        (_, t, (_, s)) = expr # (Pi t (Bind s))
        s1, s2 = type_infer(t, ctxt),\
            type_infer(s, (t,) + ctxt)
        s1, s2 = whnf(s1), whnf(s2)
        if s1[0] == s2[0] == "Const" and (s1[1], s2[1]) in PRODUCT:
            return Const(PRODUCT[s1[1], s2[1]])
        else:
            raise ValueError("Product cannot be formed.")
    elif expr[0] == "Const":
        if expr[1] in AXIOM:
            return Const(AXIOM[expr[1]])
        return "Untyped"
    elif expr[0] == "App":
        (_, m, n) = expr
        t1 = whnf(type_infer(m, ctxt)) # (Pi t3 (Bind t4))
        t2 = type_infer(n, ctxt)  # t3!
        if t1[0] == "Pi":
            (_, t3, (_, t4)) = t1
            if conv(t2, t3, ctxt):
                return subst(t4, n)
        raise ValueError("Application to a non-Pi type.")
    else:
        raise ValueError(expr)

def normal(expr):
    # print("Norm: ", pretty(expr))
    if expr[0] == "Var":
        return expr
    elif expr[0] == "Bind":
        return ("Bind", normal(expr[1]))
    elif expr[0] == "Lam":
        return ("Lam", normal(expr[1]), normal(expr[2]))
    elif expr[0] == "Pi":
        return ("Pi", normal(expr[1]), normal(expr[2]))
    elif expr[0] == "Const":
        return expr
    elif expr[0] == "App":
        e = normal(expr[1])
        if e[0] == "Lam":
            # expr == (App e=(Lam t (Bind m)) n)
            return normal(subst(e[2][1], expr[2]))
        return ("App", e, normal(expr[2]))
    else:
        raise ValueError(expr)

def conv(m, n, ctxt):
    nm, c = pretty_ctxt(ctxt)
    print_log("Conv :", c, "|-", pretty_name(m, nm), "=?", pretty_name(n, nm))
    tm0, tn0 = type_infer(m, ctxt), type_infer(n, ctxt)
    if not tm0 == tn0 == "Untyped" and not conv(tm0, tn0, ctxt):
        return False
    m, n = whnf(m), whnf(n)
    if m[0] == n[0] == "Var":
        return m[1] == n[1]
    elif m[0] == n[0] == "Bind":
        raise ValueError("Not a well-formed expression.")
    elif m[0] == n[0] == "Lam":
        (_, tm, (_, bm)) = m
        (_, tn, (_, bn)) = n
        return conv(tm, tn, ctxt) and conv(bm, bn, (tm,) + ctxt)
    elif m[0] == n[0] == "Pi":
        (_, tm, (_, bm)) = m
        (_, tn, (_, bn)) = n
        return conv(tm, tn, ctxt) and conv(bm, bn, (tm,) + ctxt)
    elif m[0] == n[0] == "Const":
        return m[1] == n[1]
    elif m[0] == n[0] == "App":
        # this is already whnf
        return conv(m[1], n[1], ctxt) and conv(m[2], n[2], ctxt)
    else:
        raise ValueError(expr)

I_expr = ("Lam",
          ("Const", "*"),
          ("Bind",
           ("Lam",
            ("Var", 0),
            ("Bind",
             ("Var", 0)))))  # \x:* -> \y:x -> x
I_type = ("Pi",
          ("Const", "*"),
          ("Bind",
           ("Pi",
           ("Var", 0),
            ("Bind",
             ("Var", 1)))))

II = App(App(I_expr, I_type), I_expr)

if __name__ == "__main__":
    print(pretty_name(I_expr), ":", pretty_name(I_type))
    print(pretty_name(normal(II)))
    print(conv(I_expr, I_expr, ()))
    print(pretty_name(type_infer(II)))
