import SubspaceBridge.SourceExterior53_242
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior53_242

theorem det3_abs_bound242 (x y z r : Fin 3 → ℝ) (a b c : ℝ)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hr : ∀ i, 0≤r i)
    (hx : ∀ i, |x i|≤a*r i) (hy : ∀ i, |y i|≤b*r i) (hz : ∀ i, |z i|≤c*r i) :
    |det3242 (x 0) (y 0) (z 0) (x 1) (y 1) (z 1) (x 2) (y 2) (z 2)| ≤
      6*(a*b*c)*(r 0*r 1*r 2) := by
  have term (u v w : Fin 3 → ℝ) (d e f : ℝ)
      (hd : 0≤d) (he : 0≤e) (hf : 0≤f)
      (hu : ∀ i, |u i|≤d*r i) (hv : ∀ i, |v i|≤e*r i) (hw : ∀ i, |w i|≤f*r i) :
      |u 0*v 1*w 2| ≤ d*e*f*(r 0*r 1*r 2) := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ (d*r 0)*(e*r 1)*(f*r 2) := mul_le_mul
        (mul_le_mul (hu 0) (hv 1) (abs_nonneg _) (mul_nonneg hd (hr 0)))
        (hw 2) (abs_nonneg _) (mul_nonneg (mul_nonneg hd (hr 0)) (mul_nonneg he (hr 1)))
      _ = _ := by ring
  have h1 := term x y z a b c ha hb hc hx hy hz
  have h2 := term y z x b c a hb hc ha hy hz hx
  have h3 := term z x y c a b hc ha hb hz hx hy
  have h4 := term z y x c b a hc hb ha hz hy hx
  have h5 := term y x z b a c hb ha hc hy hx hz
  have h6 := term x z y a c b ha hc hb hx hz hy
  have addBound {u v d e : ℝ} (hu : |u|≤d) (hv : |v|≤e) : |u+v|≤d+e :=
    (abs_add u v).trans (add_le_add hu hv)
  have subBound {u v d e : ℝ} (hu : |u|≤d) (hv : |v|≤e) : |u-v|≤d+e :=
    (abs_sub u v).trans (add_le_add hu hv)
  have h := subBound (subBound (subBound (addBound (addBound h1 h2) h3) h4) h5) h6
  unfold det3242
  convert h using 1 <;> ring

end CompoundFeasibility.Exterior53_242
