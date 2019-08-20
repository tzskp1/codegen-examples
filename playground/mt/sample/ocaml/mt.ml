(* MT19937 *)

let w = 32;;
let n = 624;;
let m = 397;;
let r = 31;;
let u = 11;;
let s = 7;;
let t = 15;;
let l = 18;;
let a = 0x9908B0DF;;
let b = 0x9D2C5680;;
let c = 0xEFC60000;;

let whole_mask = int_of_float (2.0 ** (float_of_int (w))) - 1;;
let upper_mask = int_of_float (2.0 ** (float_of_int (w-1)));;
let lower_mask = upper_mask - 1;;

type mtRand = {i: int; x: int list};;

let initialize seed =
  let rec generate acc index =
    if index = n then acc
    else generate ((1812433253 * ((List.hd acc) lxor ((List.hd acc) lsr 30)) + index) land whole_mask::acc) (index+1)
  in let l = generate [seed land whole_mask] 1
  in {i = 0; x = List.rev l};;

let rec update lst n x =
  if n = 0 then x :: (List.tl lst)
  else (List.hd lst) :: update (List.tl lst) (n-1) x;;

let next rand =
  let z = ((List.nth rand.x rand.i) land upper_mask) lor ((List.nth rand.x ((rand.i + 1) mod n)) land lower_mask) in
  let xi = (List.nth rand.x ((rand.i + m) mod n)) lxor (z lsr 1) lxor (if z land 1 = 0 then 0 else a) in
  let y0 = xi in
  let y1 = y0 lxor (y0 lsr u) in
  let y2 = y1 lxor ((y1 lsl s) land b) in
  let y3 = y2 lxor ((y2 lsl t) land c) in
  let y4 = y3 lxor (y3 lsr l) in
  (y4, {i = (rand.i + 1) mod n; x = update rand.x rand.i xi});;


let init = initialize 20150919;;

let printRandomSeq seed n =
  let rec iter index rand =
    if index = n then ()
    else
      let (nextInt, nextRand) = next rand in
      begin
        Printf.printf "%d:%d\n" index nextInt;
        iter (index+1) nextRand
      end
  in iter 0 (initialize seed);;
  
printRandomSeq 20190820 2048;;
