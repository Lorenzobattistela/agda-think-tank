data Term:
    Var(name: String)
    Abs(name: String, body: Term)
    App(func: Term, arg: Term)

data Context:
    Empty
    Extend(ctx: Context, name: String)

def inContext(name: String, ctx: Context) -> Bool:
    if ctx == Empty:
        return False
    elif ctx == Extend(ctx', name'):
        if name == name':
            return True
        else:
            return inContext(name, ctx')

def subst(t: Term, x: String, s: Term) -> Term:
    if t == Var(y):
        if x == y:
            return s
        else:
            return t
    elif t == Abs(y, t'):
        if x == y:
            return t
        else:
            return Abs(y, subst(t', x, s))
    elif t == App(t1, t2):
        return App(subst(t1, x, s), subst(t2, x, s))

def normalize(t: Term, ctx: Context) -> Term:
    if t == Var(x):
        if inContext(x, ctx):
            return t
        else:
            raise Exception("Free variable")
    elif t == Abs(x, t'):
        return Abs(x, normalize(t', Extend(ctx, x)))
    elif t == App(t1, t2):
        t1' = normalize(t1, ctx)
        t2' = normalize(t2, ctx)
        if t1' == Abs(x, t1''):
            return normalize(subst(t1'', x, t2'), ctx)
        else:
            return App(t1', t2')