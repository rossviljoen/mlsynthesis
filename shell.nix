{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  # inputsFrom = with pkgs; [ ocamlPackages.utop ];
  buildInputs = [ pkgs.ocaml pkgs.dune (import ../nix/mlcuddidl/default.nix ) pkgs.ncurses ] ++
                (with pkgs.ocamlPackages;
                  [ findlib menhir core core_bench ppx_jane re utop ]);
}

