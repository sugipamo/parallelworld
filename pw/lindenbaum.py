"""The formal layer: the part of the Lindenbaum-Tarski algebra known so far.

L_Gamma = Prop / (provable equivalence under Gamma) is a Boolean algebra. We never
hold all of it: we hold the algebra *presented* by the generators registered so
far and the relations Lean has verified. Each accepted proof takes one more
quotient of that presentation.

Closed propositions are not enough for identity (every theorem equals top), so
propositions may be built as P(a) from

  P : A -> Prop   a predicate, i.e. an element of the fibre L_Gamma(x : A)
  a : A           an object (a term)

Substitution a* : L(x : A) -> L is a Boolean homomorphism, so relations between
predicates and equalities between objects carry over to the propositions P(a).
Equalities are propagated by congruence closure.

Relation          meaning in the algebra
  holds F           [F] = top
  not F             [F] = bottom
  iff F1 F2         [F1] = [F2]
  implies F1 F2     [F1] <= [F2]
  contradiction     [F1] meet [F2] = bottom
  pred_iff P1 P2    [P1] = [P2]   in the fibre over A   ("same specification")
  pred_implies      [P1] <= [P2]  in the fibre over A   ("refines")
  obj_eq a1 a2      a1 = a2                             ("same object")
  pred_rejects P a  [P(a)] = bottom, hence [P] is not top in its fibre ("not vacuous")
  pred_disjoint     [P1] meet [P2] = bottom in the fibre ("nothing can meet both")
"""

RELATIONS = {
    "holds": "F", "not": "F", "iff": "FF", "implies": "FF", "contradiction": "FF",
    "pred_iff": "PP", "pred_implies": "PP", "obj_eq": "OO", "pred_rejects": "PO",
    "pred_disjoint": "PP",
}
_EQUATIONS = ("iff", "pred_iff", "obj_eq")


class Lindenbaum:
    def __init__(self):
        self.props = {}    # F id -> {"text", "pred": P id | None, "obj": O id | None}
        self.preds = {}    # P id -> {"type", "text"}
        self.objs = {}     # O id -> {"type", "text"}
        self.relations = []  # (relation, [ids]) exactly as verified
        self._parent = {}

    # ---- generators ------------------------------------------------------
    def add_pred(self, pid, typ, text):
        self.preds.setdefault(pid, {"type": typ, "text": text})

    def add_obj(self, oid, typ, text):
        self.objs.setdefault(oid, {"type": typ, "text": text})

    def add_prop(self, fid, text, pred=None, obj=None):
        if fid not in self.props:
            self.props[fid] = {"text": text, "pred": pred, "obj": obj}
            self._close()

    def kind(self, x):
        return "F" if x in self.props else "P" if x in self.preds else "O" if x in self.objs else None

    # ---- quotient --------------------------------------------------------
    def find(self, x):
        """Representative of the class of x under the verified equalities."""
        while self._parent.get(x, x) != x:
            self._parent[x] = self._parent.get(self._parent[x], self._parent[x])
            x = self._parent[x]
        return x

    def _union(self, a, b):
        ra, rb = sorted((self.find(a), self.find(b)))
        if ra != rb:
            self._parent[rb] = ra   # smallest id represents, so the result ignores proof order

    def relate(self, relation, ids):
        self.relations.append((relation, list(ids)))
        if relation in _EQUATIONS:
            self._union(*ids)
            self._close()

    def _close(self):
        """Congruence: equal predicates applied to equal objects are equal propositions."""
        seen = {}
        for fid, p in sorted(self.props.items()):
            if p["pred"] is None:
                continue
            key = (self.find(p["pred"]), self.find(p["obj"]))
            if key in seen:
                self._union(seen[key], fid)
            else:
                seen[key] = fid

    def classes(self, kind):
        out = {}
        for x in {"F": self.props, "P": self.preds, "O": self.objs}[kind]:
            out.setdefault(self.find(x), []).append(x)
        return out

    # ---- what the presentation says about proposition classes -------------
    def order(self):
        """Non-equational relations between proposition classes, including those that
        predicates induce on the propositions they are applied in."""
        out = set()
        for rel, ids in self.relations:
            if rel in ("holds", "not", "implies", "contradiction"):
                out.add((rel, tuple(self.find(f) for f in ids)))
            elif rel == "pred_rejects":
                for f, p in self.props.items():
                    if p["pred"] and (self.find(p["pred"]), self.find(p["obj"])) == tuple(map(self.find, ids)):
                        out.add(("not", (self.find(f),)))
            elif rel == "pred_disjoint":
                a, b = (self.find(p) for p in ids)
                for f1, p1 in self.props.items():
                    for f2, p2 in self.props.items():
                        if (p1["pred"] and p2["pred"] and self.find(p1["pred"]) == a and self.find(p2["pred"]) == b
                                and self.find(p1["obj"]) == self.find(p2["obj"])):
                            out.add(("contradiction", (self.find(f1), self.find(f2))))
            elif rel == "pred_implies":
                lo, hi = (self.find(p) for p in ids)
                for f1, p1 in self.props.items():
                    for f2, p2 in self.props.items():
                        if (p1["pred"] and p2["pred"] and self.find(p1["pred"]) == lo
                                and self.find(p2["pred"]) == hi
                                and self.find(p1["obj"]) == self.find(p2["obj"])):
                            out.add(("implies", (self.find(f1), self.find(f2))))
        return sorted(r for r in out if not (r[0] == "implies" and r[1][0] == r[1][1]))

    def decided(self):
        """Classes Lean has identified with top or bottom: constants, not unknowns."""
        return {ids[0] for rel, ids in self.order() if rel in ("holds", "not")}

    def nonvacuous(self):
        """Predicate classes with a verified counterexample: specifications that exclude something."""
        return {self.find(ids[0]) for rel, ids in self.relations if rel == "pred_rejects"}

    def disjoint(self, p1, p2):
        """Has Lean verified that no object satisfies both specifications?"""
        pair = {self.find(p1), self.find(p2)}
        return any(rel == "pred_disjoint" and {self.find(x) for x in ids} == pair for rel, ids in self.relations)
