(* An implementation of min-heaps *)

datatype 'a heap =
  Empty
| H of int * 'a * 'a heap * 'a heap  (* binary tree where each node holds size of its subtree *)

fun size h =
  case h of
    Empty => 0
  | H(n, _, _, _) => n

fun insert comp e h =
  case h of
    Empty => H(1, e, Empty, Empty)
  | H(n, root, l, r) =>
      if comp(e, root) then
        if size l <= size r
        then H(n + 1, e, insert comp root l, r)
        else H(n + 1, e, l, insert comp root r)
      else
        if size l <= size r
        then H(n + 1, root, insert comp e l, r)
        else H(n + 1, root, l, insert comp e r)

fun shift comp h =
  case h of
    Empty => Empty
  | H(_, _, Empty, Empty) => Empty
  | H(n, _, left as H(_, lr, _, _), Empty) => H(n-1, lr, shift comp left, Empty)
  | H(n, _, Empty, right as H(_, rr, _, _)) => H(n-1, rr, Empty, shift comp right)
  | H(n, _, left as H(_, lr, _, _), right as H(_, rr, _, _)) =>
      if comp(lr, rr) then
        H(n-1, lr, shift comp left, right)
      else
        H(n-1, rr, left, shift comp right)

fun remove comp h =
  case h of
    Empty => (NONE, Empty)
  | H(_, r, _, _) => (SOME r, shift comp h)
