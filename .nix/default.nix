{ }:
let
    pkgs = import <nixpkgs> {};
    stdenv = pkgs.stdenv;
    perl = pkgs.perl;
    
    isabelle = import ./isabelle {
    inherit (pkgs) stdenv fetchurl nettools perl polyml;
    inherit (pkgs.emacs24Packages) proofgeneral;
    java = if stdenv.isLinux then pkgs.jre else pkgs.jdk;
    };
in stdenv.mkDerivation {
    name = "isaenv";



    buildInputs = [ perl isabelle ];

    configurePhase = "true"; 	# Skip configure

    buildPhase = ''

      '';

# eval "${!curPhase:-$curPhase}" from nix-shell

    installPhase = "true"; # don't want to install


shellHook = ''
    curPhase=buildPhase
  '';

}
