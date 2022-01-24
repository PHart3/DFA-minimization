use "min-heap.sml";

structure bin_lex : ORD_KEY =
  struct
    type ord_key = int * int
    val compare =
      fn ((x1,x2), (y1,y2)) =>
        ( case (Int.compare (x1, y1)) of
            LESS => LESS
          | GREATER => GREATER
          | EQUAL => Int.compare (x2,y2) )
  end

fun bin_lex ((x1,x2), (y1,y2)) : bool =
  case (Int.compare (x1, y1)) of
    LESS => true
  | GREATER => false
  | EQUAL => Int.<= (x2,y2)

structure matrix = RedBlackMapFn (bin_lex)
structure RBtree = IntRedBlackMap

type DFA = {A:int list, X:int list, trans:int matrix.map, final:int list}

type data =
{inv_head : {first:int, size:int} matrix.map,
 inv_elts : int matrix.map,
 cls_head : {first:int ref, size:int ref, counter:int ref, move: int list ref} RBtree.map,
 cls_elts : (int ref) RBtree.map,
 states : {cls_of:int ref, idx_of:int ref} RBtree.map,
 L_member : (bool ref) matrix.map,
 in_class : {first:int ref, size:int ref, in_size:int ref} matrix.map,
 in_c_elts : (int ref) matrix.map,
 in_c_idx_of : (int ref) matrix.map}

val L : (int * int) heap ref = ref Empty

fun build_inv A X trans : ({first:int, size:int} matrix.map) * (int matrix.map) =
  let val init : ((int RBtree.map) * int) matrix.map =
        foldl (fn (x, M) =>
          foldl (fn (a, M') => matrix.insert (M', (x,a), (RBtree.empty,0))) M A)
        matrix.empty X
      fun construct_lists A = (
        case A of
          nil => init
        | a::ls =>
            let fun build_lists (x, table) =
                  let val b = matrix.lookup (trans, (x,a))
                      val (table_x_b, count) = matrix.lookup (table, (x,b))
                      val table_x_b_new = RBtree.insert (table_x_b, count, a)
                  in
                    matrix.insert (table, (x,b), (table_x_b_new,count + 1))
                  end
            in
              foldl build_lists (construct_lists ls) X
            end )
      val lists = construct_lists A
  in
    foldl ( fn (x, (M1,M2)) =>
      #1 ( foldl
      (fn ((a, ((m1,m2), n, m))) =>
         let val (table_x_a, count) = matrix.lookup (lists, (x,a))
             val ((mat1,mat2), index) =
               RBtree.foldl ( fn (a', ((m1',m2'), n)) =>
                 ((matrix.insert (m1', (x,a), {first=m, size=count}),
                   matrix.insert (m2', (x,n), a')),
                   n + 1)
                     ) ((m1,m2), n) table_x_a
         in
           ((mat1,mat2), index, m + count)
         end
        )
      ((M1,M2), 0, 0) A ) )
    (matrix.empty,matrix.empty) X
  end

fun build_cls A :
({first:int ref, size:int ref, counter:int ref, move: int list ref} RBtree.map)
* ((int ref) RBtree.map) *
({cls_of:int ref, idx_of:int ref} RBtree.map) =
  let val cls_and_states =
        foldl (fn (a, (l1,l2,l3,n)) =>
          (
          if n < 2 then
            RBtree.insert (l1, n+1, {first=ref 0, size=ref (length A), counter=ref 0, move=ref nil})
          else
            RBtree.insert (l1, n+1, {first=ref(~1), size=ref(~1), counter=ref(~1), move=ref nil}),
            RBtree.insert (l2, n, ref a),
            RBtree.insert (l3, a, {cls_of=ref 1, idx_of=ref n}),
            n + 1
          ) )
        (RBtree.empty, RBtree.empty, RBtree.empty, 0) A
  in
    (#1 cls_and_states, #2 cls_and_states, #3 cls_and_states)
  end

fun build_L_member A X : (bool ref) matrix.map =
  let fun range n lst : int list =
    case lst of
      nil => []
    | _::ls => n::(range (n+1) ls)
  in
      foldl (fn (x, M) =>
        foldl (fn (a, M') => matrix.insert (M', (x,a), ref false)) M (range 1 A))
      matrix.empty X
  end

fun build_inv_cls A X final (inv_head : {first:int, size:int} matrix.map) :
({first:int ref, size:int ref, in_size:int ref} matrix.map)
* ((int ref) matrix.map)
* ((int ref) matrix.map) =
  let val A' = List.filter (fn a => List.all (fn f => f <> a) final) A
      val rest =
        let fun range n lst : int list =
          case lst of
            _::a::b::ls => n::(range (n+1) (a::b::ls))
          | _ => []
        in
          range 3 A
        end
  in
    foldl (fn (x, (M1,M2,M3)) =>
      let val pre_array_x_final = foldl ( fn (a, (ls,n,m)) =>
                  if matrix.inDomain (inv_head, (x,a))
                  then
                    let val inv_head_x_a_size = #size (matrix.lookup (inv_head, (x,a)))
                    in
                      ((a,n)::ls, n + 1, m + inv_head_x_a_size)
                    end
                  else ((a,~1)::ls, n, m)
                ) (nil, 0, 0) final
          val offset_x = #2 pre_array_x_final
          val pre_array_x_A'= foldl ( fn (a, (ls,n,m)) =>
                  if matrix.inDomain (inv_head, (x,a))
                  then
                    let val inv_head_x_a_size = #size (matrix.lookup (inv_head, (x,a)))
                    in
                      ((a,n)::ls, n + 1, m + inv_head_x_a_size)
                    end
                  else ((a,~1)::ls, n, m)
                ) (nil, offset_x, 0) A'

          val array_x_A' = #1 pre_array_x_A'
          val array_x_final = #1 pre_array_x_final
          val array_x_A'_size = #3 pre_array_x_A'
          val array_x_final_size = #3 pre_array_x_final

          val array_x = array_x_final @ array_x_A'

          val length_A' = (#2 pre_array_x_A') - offset_x

          val pre_M1' = matrix.insert (M1, (x,2),
                          {first=ref 0, size=ref offset_x, in_size=ref array_x_final_size})
          val M1' = matrix.insert (pre_M1', (x,1),
                      {first=ref offset_x, size=ref length_A',
                        in_size=ref array_x_A'_size})
          val post_M1' = foldl
            (fn (n, M) => matrix.insert (M, (x,n),
                            {first=ref (~1), size=ref (~1), in_size=ref (~1)})) M1' rest
          val (M2', M3') = foldl ( fn ((a,n), (M,M')) =>
                            if n >= 0
                            then (matrix.insert (M, (x,n), ref a), matrix.insert (M', (x,a), ref n))
                            else (M, matrix.insert (M', (x,a), ref n)) )
                           (M2, M3) array_x
      in
        (post_M1', M2', M3')
      end
      ) (matrix.empty, matrix.empty, matrix.empty) X
  end

fun initialize ({A, X, trans, final} : DFA) : data =
  let val (M1, M2) = build_inv A X trans
      val (M3, M4, M5) = build_cls A
      val M6 = build_L_member A X
      val (M7, M8, M9) = build_inv_cls A X final M1
  in
    {inv_head=M1,
     inv_elts=M2,
     cls_head=M3,
     cls_elts=M4,
     states=M5,
     L_member=M6,
     in_class=M7,
     in_c_elts=M8,
     in_c_idx_of=M9}
  end

datatype Measure =
  class | x_class | inv_class

val suspects : int list ref = ref nil

val MaxClass : int ref = ref 2  (* correction *)
val Bnew : int ref = ref ~1
val hole1 : int ref = ref ~1

val in_sum : int ref = ref ~1
val s : int ref = ref ~1
val hole2 : int ref = ref ~1

fun Equivalence (autom as {A, X, trans, final} : DFA) (M : Measure) : unit =

  let val dfa = initialize autom
      val inv_head = #inv_head dfa
      val inv_elts = #inv_elts dfa
      val cls_head = #cls_head dfa
      val cls_elts = #cls_elts dfa
      val states = #states dfa
      val L_member = #L_member dfa
      val in_class = #in_class dfa
      val in_c_elts = #in_c_elts dfa
      val in_c_idx_of = #in_c_idx_of dfa

      fun Collect (x : int) (C : int) (M : Measure) : unit =

        let val (CH_first, CH_size) =
          if M = class then
            let val cls_head_C = RBtree.lookup (cls_head, C)
            in
              (!(#first cls_head_C), !(#size cls_head_C))
            end
          else
            let val in_class_x_C = matrix.lookup (in_class, (x,C))
            in
              (!(#first in_class_x_C), !(#size in_class_x_C))
            end

            fun loop_outer n size =
              if n = size then () else
                let val elt = if M = class
                              then !(RBtree.lookup (cls_elts, n))
                              else !(matrix.lookup (in_c_elts, (x,n)))
                    val inv_x_a = if matrix.inDomain (inv_head, (x,elt))
                                  then matrix.lookup (inv_head, (x,elt))
                                  else {first=(~1), size=0}
                    val inv_x_a_first = #first inv_x_a
                    fun loop_inner n size =
                      if n = size then () else
                        let val b = matrix.lookup (inv_elts, (x,n))  (* correction *)
                            val B = !(#cls_of (RBtree.lookup (states, b)))
                            val head = RBtree.lookup (cls_head, B)
                            val counter = #counter head
                            val move = #move head
                        in
                          if !counter = 0
                          then (suspects := B::(!suspects);
                               move := nil;
                               counter := !counter + 1;
                               move := b::(!move);
                               loop_inner (n + 1) size)
                          else
                            (counter := !counter + 1;
                            move := b::(!move);
                            loop_inner (n + 1) size)
                        end
                in
                  (loop_inner inv_x_a_first (#size inv_x_a + inv_x_a_first);
                   loop_outer (n + 1) size
                  )
                end
        in
          (
           suspects := nil;
           loop_outer CH_first (CH_size + CH_first)
          )
        end

      fun Split (B: int) (move: int list) : int =
        let val _ = Bnew := !MaxClass
            val _ = MaxClass := !MaxClass + 1

            val cls_head_B = RBtree.lookup (cls_head, B)
            val cls_head_B_first = #first cls_head_B
            val cls_head_B_size = #size cls_head_B

            val cls_head_Bnew = RBtree.lookup (cls_head, !Bnew)
            val cls_head_Bnew_first = #first cls_head_Bnew
            val cls_head_Bnew_size = #size cls_head_Bnew

            val move_size = length move

            fun loop lst : unit = ( case lst of
              nil => ()
            | a::ls =>
                let val states_a = RBtree.lookup (states, a)
                    val idx_of_a = #idx_of states_a
                    val apos = !idx_of_a
                    val cls_elts_hole = RBtree.lookup (cls_elts, !hole1)
                    val b = !cls_elts_hole
                    val idx_of_b = #idx_of (RBtree.lookup (states, b))
                    val cls_elts_apos = RBtree.lookup (cls_elts, apos)
                in
                  (idx_of_a := !hole1;
                   idx_of_b := apos;
                   cls_elts_hole := a;
                   cls_elts_apos := b;
                   #cls_of states_a := !Bnew;
                   hole1 := !hole1 + 1;
                   loop ls)
                end )
          in
            (hole1 := !cls_head_B_first);

            (loop move);

            (cls_head_Bnew_first := !cls_head_B_first);  (* correction *)
            (cls_head_B_first := !hole1);
            (cls_head_B_size := !cls_head_B_size - move_size);
            (cls_head_Bnew_size := move_size);

            !Bnew
          end

      fun AddBetter (B1 : int) (B2 : int) (x : int) : unit =
        let val L_member_x_B1 = matrix.lookup (L_member, (x,B1))
            val L_member_x_B2 = matrix.lookup (L_member, (x,B2))
        in
          ( case M of
              class =>
              let val cls_head_B1 = RBtree.lookup (cls_head, B1)
                  val cls_head_B1_size = !(#size cls_head_B1)
                  val cls_head_B2 = RBtree.lookup (cls_head, B2)
                  val cls_head_B2_size = !(#size cls_head_B2)
              in
                if cls_head_B1_size <= cls_head_B2_size
                then (L_member_x_B1 := true; L := (insert bin_lex (B1,x) (!L)))
                else (L_member_x_B2 := true; L := (insert bin_lex (B2,x) (!L)))
              end

            | x_class =>
              let val in_class_x_B1 = matrix.lookup (in_class, (x,B1))
                  val in_class_x_B1_size = !(#size in_class_x_B1)
                  val in_class_x_B2 = matrix.lookup (in_class, (x,B2))
                  val in_class_x_B2_size = !(#size in_class_x_B2)
              in
                if in_class_x_B1_size = 0 orelse in_class_x_B2_size = 0
                then ()
                else if in_class_x_B1_size <= in_class_x_B2_size
                then (L_member_x_B1 := true; L := (insert bin_lex (B1,x) (!L)))
                else (L_member_x_B2 := true; L := (insert bin_lex (B2,x) (!L)))
              end

            | inv_class =>
              let val in_class_x_B1 = matrix.lookup (in_class, (x,B1))
                  val in_class_x_B1_size = !(#size in_class_x_B1)
                  val in_class_x_B2 = matrix.lookup (in_class, (x,B2))
                  val in_class_x_B2_size = !(#size in_class_x_B2)
              in
                if in_class_x_B1_size = 0 orelse in_class_x_B2_size = 0
                   then ()
                   else if !(#in_size in_class_x_B1) <= !(#in_size in_class_x_B2)
                   then (L_member_x_B1 := true; L := (insert bin_lex (B1,x) (!L)))
                   else (L_member_x_B2 := true; L := (insert bin_lex (B2,x) (!L)))
              end
          )
        end

      fun SplitIncome (Old : int) (Large : int) (Small : int) : unit =
        let val cls_hd_Small = RBtree.lookup (cls_head, Small)
            val (cls_hd_Small_first, cls_hd_Small_size) =
                  (!(#first cls_hd_Small), !(#size cls_hd_Small))
            val Small_elts =
              let fun loop n size : int list =
                if n = size - 1 then []
                else (!(RBtree.lookup(cls_elts, n)))::(loop (n-1) size)
              in
                loop (cls_hd_Small_first + cls_hd_Small_size - 1) cls_hd_Small_first
              end

            fun loop_outer (X : int list) = (
              case X of
                nil => ()
              | x::xs =>
                  let val in_cls_x_Old = matrix.lookup (in_class, (x,Old))
                      val in_cls_x_Large = matrix.lookup (in_class, (x,Large))
                      val in_cls_x_Small = matrix.lookup (in_class, (x,Small))

                      val in_class_x_Old_first = #first in_cls_x_Old
                      val in_class_x_Old_size = #size in_cls_x_Old
                      val in_class_x_Old_in_size = #in_size in_cls_x_Old

                      val in_class_x_Large_first = #first in_cls_x_Large
                      val in_class_x_Large_size = #size in_cls_x_Large
                      val in_class_x_Large_in_size = #in_size in_cls_x_Large

                      val in_class_x_Small_first = #first in_cls_x_Small
                      val in_class_x_Small_size = #size in_cls_x_Small
                      val in_class_x_Small_in_size = #in_size in_cls_x_Small

                      fun loop_inner lst = ( case lst of
                        nil => ()
                      | a::ls =>
                          let val in_c_idx_of_x_a = matrix.lookup (in_c_idx_of, (x,a))
                              val apos = !in_c_idx_of_x_a
                          in
                             if apos >= 0
                             then
                               let val in_c_elts_x_hole = matrix.lookup (in_c_elts, (x,!hole2))
                                   val b = !in_c_elts_x_hole
                                   val inv_head_x_a_size = #size (matrix.lookup (inv_head, (x,a)))
                                   val in_c_idx_of_x_b = matrix.lookup (in_c_idx_of, (x,b))
                                   val in_c_elts_x_apos = matrix.lookup (in_c_elts, (x,apos))
                               in
                                 (in_sum := !in_sum + inv_head_x_a_size;
                                  in_c_idx_of_x_a := !hole2;
                                  in_c_idx_of_x_b := apos;
                                  in_c_elts_x_hole := a;
                                  in_c_elts_x_apos := b;
                                  hole2 := !hole2 + 1;
                                  s := !s + 1;
                                  loop_inner ls)
                               end
                             else ()
                          end )
                  in
                    (hole2 := !in_class_x_Old_first;
                     in_sum := 0;
                     s := 0;

                     loop_inner Small_elts;

                     in_class_x_Large_size := !in_class_x_Old_size - !s;
                     in_class_x_Small_size := !s;
                     in_class_x_Small_first := !in_class_x_Old_first;
                     in_class_x_Large_first := !hole2;
                     in_class_x_Large_in_size := !in_class_x_Old_in_size - !in_sum;
                     in_class_x_Small_in_size := !in_sum;

                     loop_outer xs)
                  end )
        in
          loop_outer X
        end

      fun Refine (lst : int list) (X : int list) : unit =
        (
        case lst of
          nil => ()
        | B :: ls =>

          let val cls_head_B = RBtree.lookup (cls_head, B)
              val cls_head_B_counter = #counter cls_head_B
              val cls_head_B_size = #size cls_head_B
          in
            if !cls_head_B_counter >= !cls_head_B_size
            then (cls_head_B_counter := 0; Refine ls X)  (* correction *)
            else
              let val cls_head_B_move = #move cls_head_B
                  val B' = Split B (!cls_head_B_move)
                  val cls_head_B' = RBtree.lookup (cls_head, B')
                  val cls_head_B'_counter = #counter cls_head_B'
                  fun loop xs = ( case xs of
                    nil => ()
                  | x :: xs =>
                      if !(matrix.lookup (L_member, (x,B)))
                      then (matrix.lookup (L_member, (x,B')) := true;
                            L := (insert bin_lex (B',x) (!L));
                            loop xs)
                      else (AddBetter B B' x;
                            loop xs) )
              in
                (cls_head_B_counter := 0;
                 cls_head_B'_counter := 0;
                 loop X;

                (
                 if M = class
                 then ()
                 else
                     if !(#size cls_head_B') <= !cls_head_B_size
                     then SplitIncome B B B'
                     else SplitIncome B B' B
                );

                Refine ls X)
              end
          end
        )
  in
    let fun loop h =
      ( case h of
          Empty => ()
        | _ =>
          let val (SOME (C,x), h') = remove bin_lex h
              val _ = L := h'
          in
            (
             (matrix.lookup (L_member, (x,C))) := false;
             Collect x C M;
             Refine (!suspects) X;
             loop (!L))
          end )
    in
      if (length final) > (length A) then print("\n\n Too many final states ")
      else if List.exists (fn f => List.all (fn a => a <> f) A) final
      then print("\n\n Invalid final state(s) ")
      else
        let val length_final = length final
        in
          if length_final = (length A) orelse length_final = 0
          then (print("\n\n Class 1: \n"); List.app (fn a => print(Int.toString(a) ^ "  ")) A)
          else

            (Split 1 final;
             List.app (fn x => AddBetter 1 2 x) X;
             loop (!L);

             RBtree.foldl
             (fn ({first,size,counter,move}, _) =>
               if !first < 0 then ()
               else
                 let val st = RBtree.lookup (cls_elts, !first)
                     val cls = #cls_of (RBtree.lookup (states, !st))
                 in
                   (
                     (
                       if (List.exists (fn f => f = !st) final)
                       then print
                       ("\n \n Class " ^ Int.toString(!cls) ^ " (final), of size "
                        ^ Int.toString(!size) ^ ":\n\n")
                       else print
                       ("\n \n Class " ^ Int.toString(!cls) ^ ", of size "
                        ^ Int.toString(!size) ^ ":\n\n")
                     );
                     let fun loop n size =
                       if n = size then ()
                       else
                         let val elt = RBtree.lookup (cls_elts, n)
                         in
                           (
                            print(Int.toString(!elt) ^ "  ");
                            loop (n + 1) size
                           )
                         end
                     in
                       loop (!first) (!first + !size)
                     end
                   )
                 end
             ) () cls_head )
        end
    end
  end

fun run_Equivalence A X final (M : Measure) (trans : (int * int * int) list) : unit =
  let val trans' = foldl (fn ((x,y,z), M) => matrix.insert (M, (x,y), z)) matrix.empty trans
  in
    (
      print("\nMinimal DFA:");
      Equivalence {A=A, X=X, trans=trans', final=final} M;
      print("\n\n");

      L := Empty;
      suspects := nil;
      MaxClass := 2;
      Bnew := ~1;
      hole1 := ~1;
      in_sum := ~1;
      s := ~1;
      hole2 := ~1
    )
  end

(*

(* A couple of examples *)

val _ = run_Equivalence [1,2,3,4,5,6,7,8] [0,1] [8] x_class
[(0,1,2), (0,2,3), (0,3,4), (0,4,5), (0,5,6), (0,6,7), (0,7,8), (0,8,8),
(1,1,1), (1,2,2), (1,3,3), (1,4,4), (1,5,5), (1,6,6), (1,7,7), (1,8,8)]

val _ = run_Equivalence [1,2,3,4,5,6] [0,1] [3,4,5] inv_class
[(0,1,2), (0,2,1), (1,1,3), (1,2,4), (1,3,6), (0,3,5),
 (0,4,5), (1,4,6), (0,5,5), (1,5,6), (0,6,6), (1,6,6)]

*)
