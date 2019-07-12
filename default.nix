{ compiler ? "ghc865", pkgs ? import <nixpkgs> {} }:

let
	haskellPackages = pkgs.haskell.packages.${compiler};
	drv = haskellPackages.callCabal2nix "recover" ./. {};
in {
	recover = drv;
	recover-shell = haskellPackages.shellFor {
		packages = p: [drv];
		buildInputs = with pkgs; [ ];
	};
}
