# RelativeSerreCurves

This is code for the preprint [Serre Curves Relative to Obstructions Modulo 2](https://arxiv.org/abs/2210.06645) by Jacob Mayle and Rakvi.

The main function is `IsRelSerreCurve`, which given an elliptic curve E/Q, outputs <true, G> if E is a G-Serre curve for a proper subgroup G of GL(2,Z/2Z), and outputs false otherwise. The functions `ImgCondCs`, `ImgCondB`, `ImgCondCn` compute the image conductor, and `CyclicityCorrectionFactorB` and `CyclicityCorrectionFactorCn` compute the cyclicity correction factor for the corresponding relative Serre curves. There are also several functions that are referenced in the paper. Finally, `AdelicImageExample1`, `AdelicImageExample2`, and `AdelicImageExample3` compute the adelic Galois image of the elliptic curves with LMFDB label 315.a2, 69.a1, and 392.a1 as explained in Example 5.1, 5.2, and 5.3 (respectively).

Installation instructions:
1. Install the latest version of Magma from [http://magma.maths.usyd.edu.au/magma/](http://magma.maths.usyd.edu.au/magma/).
2. Download "ell-adic-galois-images" from [https://github.com/AndrewVSutherland/ell-adic-galois-images](https://github.com/AndrewVSutherland/ell-adic-galois-images).
4. Move the folder "ell-adic-galois-images-main" to Magma's directory folder (use the `GetCurrectDirectory()` command in Magma to see the current directory).
5. Download "galrep" from [https://math.mit.edu/~drew/galrep/](https://math.mit.edu/~drew/galrep/) and move the folder as in Step 4.
6. Download and run "RelSerreCurve.m" from [https://github.com/maylejacobj/RelativeSerreCurves](https://github.com/maylejacobj/RelativeSerreCurves).

Please contact us with any questions, comments, or suggestions.
