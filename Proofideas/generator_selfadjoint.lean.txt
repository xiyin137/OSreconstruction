/-
Proof plan for generator_selfadjoint: 𝒰.generator.IsSelfAdjoint
  (i.e., A = A* where A is the infinitesimal generator of a strongly continuous
  one-parameter unitary group U(t))

APPROACH: Use eq_of_graph_eq. Show graph(A) = graph(A*).
  graph(A) ⊆ graph(A*) from symmetry (already in symmetric_closable proof).
  graph(A*) ⊆ graph(A): the hard direction.

For graph(A*) ⊆ graph(A):
  Let (y, z) ∈ graph(A*), i.e., y ∈ dom(A*) and A*y = z.
  Need to show y ∈ dom(A) and Ay = z.

KEY LEMMA: ker(A* - i) = {0} and ker(A* + i) = {0}.
  (Once we have this + Ran(A-i) = H, the domain inclusion follows.)

PROOF OF ker(A* - i) = {0}:
  Let v ∈ dom(A*) with A*v = iv.
  For x ∈ dom(A), define g(t) = ⟨U(t)x, v⟩ : ℝ → ℂ.

  Step 1: Show g is differentiable with g'(t) = g(t).
    g(t+h) - g(t) = ⟨U(t)(U(h)x - x), v⟩
    (1/h)(g(t+h) - g(t)) = ⟨U(t)((1/h)(U(h)x - x)), v⟩ → ⟨U(t)(iAx), v⟩ = ⟨iU(t)(Ax), v⟩

    Now: ⟨iU(t)(Ax), v⟩ = (-i)⟨U(t)(Ax), v⟩ = (-i)⟨Ax, U(-t)v⟩
    Using U(-t)v ∈ dom(A*) and A*(U(-t)v) = U(-t)(A*v) = iU(-t)v:
    ⟨Ax, U(-t)v⟩ = ⟨x, A*(U(-t)v)⟩ = ⟨x, iU(-t)v⟩ = i⟨x, U(-t)v⟩ = i⟨U(t)x, v⟩ = ig(t)
    So g'(t) = (-i)(ig(t)) = g(t).

  Step 2: g(t) = g(0)eᵗ (unique solution to g' = g).
    Define h(t) = e^{-t}g(t). HasDerivAt h 0 t (product rule, g'=g cancels).
    h constant ⟹ h(t) = h(0) = g(0) ⟹ g(t) = g(0)eᵗ.

  Step 3: |g(t)| ≤ ‖x‖‖v‖ for all t (since U(t) isometric).
    eᵗg(0) bounded ⟹ g(0) = 0 for all t ∈ ℝ.
    So ⟨x, v⟩ = g(0) = 0 for all x ∈ dom(A).
    dom(A) dense ⟹ v = 0.

PROOF OF ker(A* + i) = {0}: Same argument with α = -1.
  g'(t) = -g(t), g(t) = g(0)e^{-t}.
  Bounded on ℝ (including t → -∞ where e^{-t} → ∞) ⟹ g(0) = 0.

HELPER LEMMAS NEEDED:
  1. U(t) preserves dom(A): U(t)x ∈ dom(A) for x ∈ dom(A), and A(U(t)x) = U(t)(Ax).
     Proof: h⁻¹(U(h)(U(t)x) - U(t)x) = U(t)(h⁻¹(U(h)x - x)) → U(t)(iAx).

  2. U(t) preserves dom(A*): U(t)v ∈ dom(A*) for v ∈ dom(A*), and A*(U(t)v) = U(t)(A*v).
     Proof: For z ∈ dom(A): ⟨Az, U(t)v⟩ = ⟨U(-t)(Az), v⟩ = ⟨A(U(-t)z), v⟩ (by #1)
     = ⟨U(-t)z, A*v⟩ = ⟨z, U(t)(A*v)⟩. Boundedness: |⟨Az, U(t)v⟩| ≤ ‖A*v‖·‖z‖.

  3. A is closed (needed for closed range of A ± i).
     Proof: If x_n → x and Ax_n → y, use integral formula
     U(t)x_n - x_n = i∫₀ᵗ U(s)(Ax_n) ds → i∫₀ᵗ U(s)y ds = U(t)x - x.
     Then t⁻¹(U(t)x - x) = it⁻¹∫₀ᵗ U(s)y ds → iy.
     So I⁻¹·t⁻¹(U(t)x - x) → I⁻¹·iy = y. Hence x ∈ dom(A), Ax = y.

  4. ‖(A ± i)x‖² = ‖Ax‖² + ‖x‖² (algebraic, from symmetry).
     In particular ‖(A-i)x‖ ≥ ‖x‖.

  5. Ran(A - i) is closed (A closed + bounded below).
  6. Ran(A - i)⊥ ⊆ ker(A* + i) (algebraic).
  7. Ran(A - i) = H (dense + closed).

COMPLETING THE PROOF:
  For y ∈ dom(A*): (A* - i)y ∈ H = Ran(A - i).
  So ∃ z ∈ dom(A) with (A - i)z = (A* - i)y.
  Since A ⊆ A*: (A* - i)(y - z) = 0, so y - z ∈ ker(A* - i) = {0}.
  Therefore y = z ∈ dom(A) and A*y = Ay (by symmetry on dom(A)).
-/
