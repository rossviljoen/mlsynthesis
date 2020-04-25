{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  # inputsFrom = with pkgs; [ ocamlPackages.utop ];
  buildInputs = [ pkgs.ocaml pkgs.dune (import ../nix/mlcuddidl/default.nix ) pkgs.ncurses ] ++
                (with pkgs.ocamlPackages;
                  [ findlib menhir core ppx_jane ppx_deriving utop ]);
}

