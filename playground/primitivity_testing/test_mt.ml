(* inverse decimation method MT19937 *)

let w = 32;;
let n = 624;;
let m = 397;;
let r = 31;;
let p = w * n - r;;

let upper_mask = int_of_float (2.0 ** (float_of_int (w-1)));;
let lower_mask = upper_mask - 1;;

let bottom_zero_mask = int_of_float (2.0 ** (float_of_int w)) - 2;;
let bottom_one_mask = 1;;

type mtRand = {index: int; state: int array};;

let copy_words words = Array.copy words

let make_mtRand state = {index = 0; state = copy_words state};;

let set_nth_word words n x = (Array.set words n x; words);;

let nth_word words n = (Array.get words n);;

let next a rand =
  let z = ((nth_word rand.state rand.index) land upper_mask)
          lor ((nth_word rand.state ((rand.index + 1) mod n)) land lower_mask) in
  let xi = (nth_word rand.state ((rand.index + m) mod n)) lxor (z lsr 1) lxor (if z land 1 = 0 then 0 else a) in
  (xi, {index = (rand.index + 1) mod n; state = set_nth_word rand.state rand.index xi});;
     
let rec generate a words rand times =
  if times = 0
  then words
  else
    let (nextValue, nextRand) = next a rand in
    generate a (set_nth_word words (2 * p - times) nextValue) nextRand (times-1);;

let decimate words = 
  let rec aux acc j =
    if j > p
    then  acc
    else aux (set_nth_word acc j (nth_word acc (2 * j - 1))) (j + 1)
  in
    aux words 1;;

let process a words =
  let rand = make_mtRand words in
  let expandedWords = generate a words rand (2 * p - n) in
  let decimatedWords = decimate expandedWords in
  let rec aux words k =
    if k < n
    then words
    else
      let xk = nth_word words k in
      let xkn = nth_word words (k-n) in
      let xknm = nth_word words (k-n+m) in
      let xkn1 = nth_word words (k-n+1) in
      let y = xk lxor xknm lxor  (if xkn1 land 1 = 0 then 0 else a) in
      let y1 = y lsl 1 in
      let y2 = if xkn1 land 1 = 0
               then
                 y1 land bottom_zero_mask
               else
                 y1 lor bottom_one_mask
      in
      let newxkn1 = (upper_mask land xkn1) lor (lower_mask land y2) in
      let newxkn = (upper_mask land y2) lor (lower_mask land xkn) in
      let words1 = set_nth_word words (k-n+1) newxkn1 in
      let words2 = set_nth_word words1 (k-n) newxkn in
      aux words2 (k - 1)
    in
      aux decimatedWords p;;

let rec process_rec a words times =
  if times = 0
  then words
  else process_rec a (process a words) (times - 1);;

let check initial_words last_words = 
  if (upper_mask land (nth_word last_words 0)) != ((nth_word initial_words 0) land upper_mask)
  then false
  else
    let rec aux initial last index =
      if index = n then true
      else ((nth_word initial index) = (nth_word last index)) && aux initial last (index+1)
    in
       aux initial_words last_words 1;;

let initial_words () = Array.init (2 * p) (fun x -> x);;

let test_ml a = 
  let last_words = process_rec a (initial_words ()) p
  in
    check (initial_words ()) last_words;;

let a = 0x9908B0DF;;
let a1 = 0x9908B0DD;;

print_string (if test_ml a then "ok" else "ng");;
