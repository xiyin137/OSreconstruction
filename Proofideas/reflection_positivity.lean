/-
  Proof Ideas: E2 Reflection Positivity
  (os_inner_product_eq_wightman_positivity)

  Goal: Show that for F supported at positive times,
    ⟨F,F⟩_OS = Σ_{n,m} S_{n+m}((θf̄ₙ) ⊗ fₘ) ≥ 0

  where S is constructed from Wightman functions via BHW analytic continuation:
    S_k(h) = ∫ F_ext(Wick(x)) · h(x) dx

  KEY MATHEMATICAL ARGUMENT (OS I, Section 5; Glimm-Jaffe Ch. 19):

  1. EXPANDING THE OS INNER PRODUCT:
     ⟨F,F⟩_OS = Σ_{n,m} S_{n+m}((θf̄ₙ) ⊗ fₘ)
     = Σ_{n,m} ∫_{ℝ^{(n+m)(d+1)}} F_ext(Wick(y₁,...,yₙ,x₁,...,xₘ)) ·
         conj(fₙ(θy₁,...,θyₙ)) · fₘ(x₁,...,xₘ) dy₁...dyₙ dx₁...dxₘ

     where yᵢ range over negative times (since f is at positive times, θf̄ is at negative times)
     and xⱼ range over positive times.

  2. WICK ROTATION AND BOUNDARY VALUES:
     At Euclidean points y = (-τ₁,ȳ₁,...,-τₙ,ȳₙ, σ₁,x̄₁,...,σₘ,x̄ₘ) with τᵢ > 0, σⱼ > 0:
     Wick(y) = (-iτ₁,ȳ₁,...,-iτₙ,ȳₙ, iσ₁,x̄₁,...,iσₘ,x̄ₘ)

     The first n points have NEGATIVE imaginary time, the last m have POSITIVE imaginary time.

  3. THE KEY IDENTITY: RELATING OS AND WIGHTMAN INNER PRODUCTS
     The analytic continuation F_ext connects the two via:

     F_ext(Wick(-τ₁,ȳ₁,...,-τₙ,ȳₙ, σ₁,x̄₁,...,σₘ,x̄ₘ))
     = F_ext(-iτ₁,ȳ₁,...,-iτₙ,ȳₙ, iσ₁,x̄₁,...,iσₘ,x̄ₘ)

     By BHW analytic continuation (BHW property: holomorphic on PET),
     this equals the Wightman function evaluated at the corresponding
     Minkowski point configuration via the boundary value formula:

     = lim_{ε→0+} W_{n+m}(ȳₙ-iε·η_n,...,ȳ₁-iε·η₁, x̄₁+iε·η₁,...,x̄ₘ+iε·ηₘ)

     where the argument ORDER is REVERSED for the first n points!

     More precisely, the Euclidean time-reflection Θ combined with Wick rotation
     produces the BORCHERS INVOLUTION (argument reversal + conjugation) of the
     Wightman theory:

     (θf̄ₙ)(y) at Wick-rotated points ↔ f̄ₙ^rev(x) at Minkowski points

  4. THE POSITIVITY ARGUMENT:
     After this identification:
     ⟨F,F⟩_OS = ⟨F',F'⟩_W (modulo the Wick rotation identification)
     where F' is the corresponding sequence in the Wightman setting.

     Since W satisfies positive definiteness (R2), ⟨F',F'⟩_W.re ≥ 0.
     Therefore ⟨F,F⟩_OS.re ≥ 0.

  5. DETAILED COMPUTATION FOR EACH (n,m) TERM:
     Fix n, m. The (n,m) term of ⟨F,F⟩_OS is:
       ∫ F_ext(Wick(y₁,...,yₙ,x₁,...,xₘ)) · conj(fₙ(-Θy₁,...,-Θyₙ)) · fₘ(x₁,...,xₘ) dy dx

     Substitution: yᵢ = (-τᵢ, ȳᵢ) → (τᵢ, ȳᵢ) (flip time in yᵢ, Jacobian = 1):
       ∫ F_ext(Wick(θ(τ₁,ȳ₁),...,θ(τₙ,ȳₙ),(σ₁,x̄₁),...,(σₘ,x̄ₘ)))
         · conj(fₙ(τ₁,ȳ₁,...,τₙ,ȳₙ)) · fₘ(σ₁,x̄₁,...,σₘ,x̄ₘ) dτ dȳ dσ dx̄

     Now use the HERMITICITY of F_ext:
       F_ext(-iτ₁,ȳ₁,...,-iτₙ,ȳₙ,iσ₁,x̄₁,...,iσₘ,x̄ₘ)
       = conj(F_ext(iτₙ,ȳₙ,...,iτ₁,ȳ₁,-iσₘ,x̄ₘ,...,-iσ₁,x̄₁))   (*)

     Wait — this uses Hermiticity of Wightman functions W(x₁,...,xₖ)* = W(xₖ,...,x₁).

     Actually, the more direct approach:

  6. ALTERNATIVE: DIRECT DISTRIBUTIONAL APPROACH
     The key is that the Schwinger functions S_{n+m} are the BOUNDARY VALUES of the
     BHW analytic continuation. Specifically:

     S_{n+m}((θf̄ₙ) ⊗ fₘ) = lim_{ε→0+} ∫ W_{n+m}(... Minkowski config ...)
                                              · ((θf̄ₙ) ⊗ fₘ)(Euclidean config) dx

     This can be related term-by-term to the Wightman inner product.

  7. SIMPLEST APPROACH — FACTORING THROUGH THE BOUNDARY VALUE:
     For positive-time supported f, the Euclidean points are deep in the tube.
     The BHW extension at these points EQUALS the boundary value of W_analytic.
     The Wick-rotated positive time region maps into the forward tube.

     Key: For τ > 0, Wick(τ,x⃗) = (iτ,x⃗) which has Im(z₀) = τ > 0.
     For τ < 0, Wick(τ,x⃗) = (iτ,x⃗) which has Im(z₀) = τ < 0.

     So for the (n,m)-term with θf̄ₙ at negative times and fₘ at positive times:
     The first n Wick-rotated points have Im(z₀) < 0 (BACKWARD tube).
     The last m Wick-rotated points have Im(z₀) > 0 (FORWARD tube).

     The combined configuration (backward ∪ forward) lives in the permuted extended tube.

     Now use: at these points, F_ext = W_analytic (the holomorphic extension of W).

  IMPLEMENTATION PLAN:
  - Step A: Show the OS inner product can be written as an integral over W_analytic
            evaluated at Wick-rotated configurations
  - Step B: Show this integral equals the Wightman inner product (via the change of
            variables: Euclidean time-reflection ↔ Borchers argument reversal)
  - Step C: Apply Wightman positive definiteness

  DEPENDENCIES:
  - BHW extension evaluated at Euclidean points = W_analytic
  - Hermiticity of W (axiom R5)
  - Positive definiteness of W (axiom R2)
  - Change of variables (time reflection is measure-preserving)

  STATUS: Not started. Need to check if the formal definitions match this argument.
-/
