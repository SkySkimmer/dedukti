open Dkterm
open Coqine
open Names
open Declarations
open Term

let add_rec_path ~unix_path:dir ~coq_root:coq_dirpath =
  let dirs = System.all_subdirs dir in
  let prefix = repr_dirpath coq_dirpath in
  let convert_dirs (lp,cp) =
    (lp,make_dirpath (List.rev_map id_of_string cp@prefix)) in
  let dirs = Util.map_succeed convert_dirs dirs in
    List.iter Check.add_load_path dirs;
    Check.add_load_path (dir,coq_dirpath)


let prefix = ref ""

let add_path p =
  add_rec_path p (make_dirpath (if !prefix = "" then [] else [id_of_string !prefix]))


let speclist = Arg.align
 [ "-r", Arg.Set_string prefix, "Id";
    "--root", Arg.Set_string prefix, "Id set the dirpath root as Id\n";
    "-I", Arg.String add_path, "path";
    "--include", Arg.String add_path, "path add path using the current dirpath root\n";
    "-p", Arg.Unit pp_prefix, "";
    "--prefix-notation", Arg.Unit pp_prefix, " use Dedukti prefix syntax (faster parsing, default)\n";
    "-h", Arg.Unit pp_external, "";
    "--external", Arg.Unit pp_external, " use Dedukti external syntax (more human readable)\n";
]


let translate filename =
  let channel = open_in_bin filename in
  let i = input_binary_int channel in
  if i <> 8300 then Printf.fprintf stderr "Warning: the magic number of %s, which is %d, does not correspond to the version of Coq handled by CoqInE, which is 8.3. Expect strange behaviours." filename i;
  let (md:Check.library_disk) = Marshal.from_channel channel in
  close_in channel;
  let ml = (md.Check.md_name, filename) in
      (* Putting dependancies in the environment *)
  let needed = List.rev (Check.intern_library Check.LibrarySet.empty ml []) in
  Coqine.base_env :=
    List.fold_left
    (fun env (dir,m) ->
      if dir <> md.Check.md_name then
        Safe_typing.unsafe_import
          m.Check.library_compiled m.Check.library_digest env
      else env )
    (Coqine.get_base_env ()) needed;
  let path,mb = Safe_typing.path_mb_compiled_library md.Check.md_compiled in
  print_decls (path_to_string path) (mb_trans (MPfile path) mb)

let _ =
(*  add_rec_path "/usr/lib/coq/theories" ["Coq"];*)
  Arg.parse speclist translate
    "CoqInE\nUsage: coqine [options] filenames\n\nIf you want to use the coq library,\nuse --root Coq -I path_to_coq_dir_theories\n\nfilenames:\tcoq binary files (.vo)\n\noptions:"
