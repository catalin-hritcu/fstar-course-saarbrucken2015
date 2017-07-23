module DynACLs

open FStar.Heap
open FStar.ST
open FStar.List

type file = string
      
(* using dynamic ACLs in some database *)
type entry = 
  | Readable of string
  | Writable of string
type db = list entry 
assume val acls: ref db

val canWrite : db -> file -> Tot bool
let canWrite db file = 
  is_Some (find (function Writable x -> x=file | _ -> false) db)

val canRead : db -> file -> Tot bool
let canRead db file = 
  is_Some (find (function Readable x | Writable x -> x=file) db)
  

type CanRead f h  = canRead  (Heap.sel h acls) f == true
type CanWrite f h = canWrite (Heap.sel h acls) f == true

(* F* infers precise specifications for all non-recursive effectful computations *)
let grant e = 
  let a = read acls in 
  write acls (e::a)

let revoke e = 
  let a = read acls in
  let db = filter (fun e' -> e<>e') a in
  write acls db

(* two dangerous primitives *)
assume val read:   file:string -> ST string 
                                     (requires (CanRead file))
                                     (ensures (fun h s h' -> h=h'
                                      /\ modifies Set.empty h h'))

assume val delete: file:string -> ST unit
                                     (requires (CanWrite file))
                                     (ensures (fun h s h' -> h=h'
                                      /\ modifies Set.empty h h'))

val safe_delete: file -> All unit (fun h -> True) (fun h x h' -> h==h')
let safe_delete file = 
  if canWrite !acls file 
  then delete file
  else failwith "unwritable"

val test_acls: file -> unit
let test_acls f = 
  grant (Readable f);     (* ok *)
  let _ = read f in       (* ok --- it's in the acl *)
  (* delete f;               not ok --- we're only allowed to read it *)
  safe_delete f;          (* ok, but fails dynamically *)
  revoke (Readable f)
  (* ;read f                  not ok any more *)
