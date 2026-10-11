import VerifiedGarbage.Proof.Modes.Ops
import VerifiedGarbage.Spec.Ofb
import VerifiedGarbage.Spec.Cfb
import VerifiedGarbage.Spec.Cfb8
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The modes, one step at a time, for any target

A mode is a machine (`StepFn`): from the chaining value (or CFB8's input
block) and a step's input, the step's output and the next chaining value.
`run F c xs` runs it over the steps `xs` from `c`, and gives the outputs and
the last chaining value. Each mode of SP 800-38A here is `run` of its step
function (`encrypt_run`, `ofb_run`, …): CBC, OFB, CFB with segments of a
block, and CFB8, whose steps are single bytes.

`Computes M L ciph F`: the mode's operations (`Impl.Modes.Mode`), with the
block cipher `ciph` on blocks of `L` bytes in `buf` between `pre` and
`post`, compute `F` from the data and chaining value areas. Each mode of
`Impl/Modes/Ops.lean` computes its step function (`cbcEnc_computes`, …).
Nothing here depends on a target.
-/

namespace VG.Proof.Modes

open VG VG.Impl.Modes
open VG.Spec.Cbc (Cipher xor)

/-- A mode's step: from the chaining value and the step's input, the output
and the next chaining value. -/
abbrev StepFn := List Byte → List Byte → List Byte × List Byte

/-- The outputs of the steps `xs` from `c`, and the last chaining value. -/
def run (F : StepFn) : List Byte → List (List Byte) → List (List Byte) × List Byte
  | c, [] => ([], c)
  | c, x :: xs => let r := F c x; let q := run F r.2 xs; (r.1 :: q.1, q.2)

theorem run_snoc (F : StepFn) : ∀ (c : List Byte) (xs : List (List Byte)) (x : List Byte),
    run F c (xs ++ [x]) = ((run F c xs).1 ++ [(F (run F c xs).2 x).1], (F (run F c xs).2 x).2)
  | _, [], _ => rfl
  | c, y :: ys, x => by simp only [List.cons_append, run, run_snoc F _ ys x]

theorem run_length (F : StepFn) : ∀ (c : List Byte) (xs : List (List Byte)), (run F c xs).1.length = xs.length
  | _, [] => rfl
  | _, _ :: xs => by simp only [run, List.length_cons, run_length F _ xs]

/-! ## The modes' steps -/

/-- CBC encryption: `Cⱼ = CIPH_K(Pⱼ ⊕ Cⱼ₋₁)`, the output and the next
chaining value. -/
def cbcEncF (ciph : Cipher) : StepFn := fun c x => let y := ciph (xor x c); (y, y)

/-- CBC decryption: `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁`; `Cⱼ` the next chaining value. -/
def cbcDecF (ciph : Cipher) : StepFn := fun c x => (xor (ciph x) c, x)

/-- OFB: `Oⱼ = CIPH_K(Oⱼ₋₁)` the next chaining value, `Xⱼ ⊕ Oⱼ` the output. -/
def ofbF (ciph : Cipher) : StepFn := fun c x => let o := ciph c; (xor x o, o)

/-- CFB encryption: `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, the output and the next chaining
value. -/
def cfbEncF (ciph : Cipher) : StepFn := fun c x => let y := xor x (ciph c); (y, y)

/-- CFB decryption: `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`; `Cⱼ` the next chaining value. -/
def cfbDecF (ciph : Cipher) : StepFn := fun c x => (xor x (ciph c), x)

/-- CFB8 encryption of a byte `[P#ⱼ]`: `C#ⱼ = P#ⱼ ⊕ MSB₈(CIPH_K(Iⱼ))`, and
`Iⱼ₊₁`, `Iⱼ` without its first byte, followed by `C#ⱼ`. -/
def cfb8EncF (ciph : Cipher) : StepFn := fun c x =>
  let y := x.headD 0 ^^^ (ciph c).headD 0; ([y], c.tail ++ [y])

/-- CFB8 decryption of a byte `[C#ⱼ]`: `P#ⱼ = C#ⱼ ⊕ MSB₈(CIPH_K(Iⱼ))`, and
`Iⱼ₊₁` with `C#ⱼ`. -/
def cfb8DecF (ciph : Cipher) : StepFn := fun c x =>
  ([x.headD 0 ^^^ (ciph c).headD 0], c.tail ++ [x.headD 0])

theorem encrypt_run (ciph : Cipher) : ∀ (iv : List Byte) (xs : List (List Byte)),
    Spec.Cbc.encrypt ciph iv xs = (run (cbcEncF ciph) iv xs).1
  | _, [] => rfl
  | iv, x :: xs => by rw [Spec.Cbc.encrypt, encrypt_run ciph _ xs]; rfl

theorem decrypt_run (ciph : Cipher) : ∀ (iv : List Byte) (xs : List (List Byte)),
    Spec.Cbc.decrypt ciph iv xs = (run (cbcDecF ciph) iv xs).1
  | _, [] => rfl
  | iv, x :: xs => by rw [Spec.Cbc.decrypt, decrypt_run ciph _ xs]; rfl

theorem ofb_run (ciph : Cipher) : ∀ (iv : List Byte) (xs : List (List Byte)),
    Spec.Ofb.crypt ciph iv xs = (run (ofbF ciph) iv xs).1 ∧
      Spec.Ofb.next ciph iv xs.length = (run (ofbF ciph) iv xs).2
  | _, [] => ⟨rfl, rfl⟩
  | iv, x :: xs => by
    obtain ⟨h1, h2⟩ := ofb_run ciph (ciph iv) xs
    refine ⟨?_, ?_⟩
    · simp only [Spec.Ofb.crypt, List.length_cons, Spec.Ofb.outputs, List.zipWith_cons_cons] at h1 ⊢
      rw [h1]; rfl
    · simp only [Spec.Ofb.next, List.length_cons, Spec.Ofb.outputs] at h2 ⊢
      rw [List.getLastD_cons, h2]; rfl

theorem cfbEnc_run (ciph : Cipher) : ∀ (iv : List Byte) (xs : List (List Byte)),
    Spec.Cfb.encrypt ciph iv xs = (run (cfbEncF ciph) iv xs).1 ∧
      Spec.Cbc.next iv (Spec.Cfb.encrypt ciph iv xs) = (run (cfbEncF ciph) iv xs).2
  | _, [] => ⟨rfl, rfl⟩
  | iv, x :: xs => by
    obtain ⟨h1, h2⟩ := cfbEnc_run ciph (xor x (ciph iv)) xs
    refine ⟨by rw [Spec.Cfb.encrypt, h1]; rfl, ?_⟩
    rw [Spec.Cfb.encrypt, Spec.Cbc.next, List.getLastD_cons, ← Spec.Cbc.next, h2]; rfl

theorem cfbDec_run (ciph : Cipher) : ∀ (iv : List Byte) (xs : List (List Byte)),
    Spec.Cfb.decrypt ciph iv xs = (run (cfbDecF ciph) iv xs).1 ∧
      Spec.Cbc.next iv xs = (run (cfbDecF ciph) iv xs).2
  | _, [] => ⟨rfl, rfl⟩
  | iv, x :: xs => by
    obtain ⟨h1, h2⟩ := cfbDec_run ciph x xs
    refine ⟨by rw [Spec.Cfb.decrypt, h1]; rfl, ?_⟩
    rw [Spec.Cbc.next, List.getLastD_cons, ← Spec.Cbc.next, h2]; rfl

/-- A string of bytes as CFB8's steps. -/
def bytesSteps (bs : List Byte) : List (List Byte) := bs.map fun b => [b]

theorem bytesSteps_flatten : ∀ bs : List Byte, (bytesSteps bs).flatten = bs
  | [] => rfl
  | b :: bs => by
    simp only [bytesSteps, List.map_cons, List.flatten_cons, List.singleton_append]
    exact congrArg _ (bytesSteps_flatten bs)

theorem cfb8_drop (iv cs : List Byte) (c : Byte) (hiv : iv ≠ []) :
    Spec.Cfb8.next (iv.tail ++ [c]) cs = Spec.Cfb8.next iv (c :: cs) := by
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hiv
  simp [Spec.Cfb8.next]

theorem cfb8Enc_run (ciph : Cipher) : ∀ (iv : List Byte) (bs : List Byte), iv ≠ [] →
    Spec.Cfb8.encrypt ciph iv bs = (run (cfb8EncF ciph) iv (bytesSteps bs)).1.flatten ∧
      Spec.Cfb8.next iv (Spec.Cfb8.encrypt ciph iv bs) = (run (cfb8EncF ciph) iv (bytesSteps bs)).2
  | _, [], _ => ⟨rfl, by simp [Spec.Cfb8.next, Spec.Cfb8.encrypt, bytesSteps, run]⟩
  | iv, b :: bs, hiv => by
    have hne : iv.tail ++ [b ^^^ (ciph iv).headD 0] ≠ [] := by simp
    obtain ⟨h1, h2⟩ := cfb8Enc_run ciph _ bs hne
    refine ⟨by rw [Spec.Cfb8.encrypt, h1]; rfl, ?_⟩
    rw [Spec.Cfb8.encrypt, ← cfb8_drop iv _ _ hiv, h2]; rfl

theorem cfb8Dec_run (ciph : Cipher) : ∀ (iv : List Byte) (bs : List Byte), iv ≠ [] →
    Spec.Cfb8.decrypt ciph iv bs = (run (cfb8DecF ciph) iv (bytesSteps bs)).1.flatten ∧
      Spec.Cfb8.next iv bs = (run (cfb8DecF ciph) iv (bytesSteps bs)).2
  | _, [], _ => ⟨rfl, by simp [Spec.Cfb8.next, bytesSteps, run]⟩
  | iv, b :: bs, hiv => by
    have hne : iv.tail ++ [b] ≠ [] := by simp
    obtain ⟨h1, h2⟩ := cfb8Dec_run ciph _ bs hne
    refine ⟨by rw [Spec.Cfb8.decrypt, h1]; rfl, ?_⟩
    rw [← cfb8_drop iv _ _ hiv, h2]; rfl

/-! ## The operations compute the steps -/

/-- The first `n` bytes of area `l`. -/
def rd (a : Areas) (l : Loc) (n : Nat) : List Byte := (List.range n).map (a l)

theorem rd_length (a : Areas) (l : Loc) (n : Nat) : (rd a l n).length = n := by simp [rd]

theorem getD_rd {a : Areas} {l : Loc} {n i : Nat} (hi : i < n) : (rd a l n).getD i 0 = a l i := by
  simp [rd, List.getD_eq_getElem?_getD, hi]

/-- `rd` from each byte. -/
theorem rd_eq {a : Areas} {l : Loc} {n : Nat} {xs : List Byte} (hl : xs.length = n)
    (h : ∀ i < n, a l i = xs.getD i 0) : rd a l n = xs := by
  apply List.ext_getElem (by rw [rd_length, hl])
  intro i h1 _
  have hi : i < n := by rw [rd_length] at h1; exact h1
  rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0, getD_rd hi, h i hi]

/-- The block cipher `ciph` on the first `n` bytes of `buf`. -/
def cryptBuf (n : Nat) (ciph : Cipher) (a : Areas) : Areas := fun l i =>
  if l = .buf then (ciph (rd a .buf n)).getD i 0 else a l i

/-- One step: `pre`, the block cipher on `buf`, `post`. -/
def stepA (M : Mode) (n : Nat) (ciph : Cipher) (a : Areas) : Areas :=
  applyOps M.post (cryptBuf n ciph (applyOps M.pre a))

/-- `M`'s operations compute `F`, with the block cipher `ciph` on blocks of
`L` bytes. -/
def Computes (M : Mode) (L : Nat) (ciph : Cipher) (F : StepFn) : Prop :=
  ∀ a, rd (stepA M L ciph a) .dat M.step = (F (rd a .chn L) (rd a .dat M.step)).1 ∧
    rd (stepA M L ciph a) .chn L = (F (rd a .chn L) (rd a .dat M.step)).2

theorem getD_xor {x y : List Byte} {i : Nat} (hx : i < x.length) (hy : i < y.length) :
    (xor x y).getD i 0 = x.getD i 0 ^^^ y.getD i 0 := by
  have h : i < (xor x y).length := by simp [Spec.Cbc.xor]; omega
  rw [← List.getElem_eq_getD (h := h), ← List.getElem_eq_getD (h := hx), ← List.getElem_eq_getD (h := hy)]
  simp [Spec.Cbc.xor]

theorem xor_length (x y : List Byte) : (xor x y).length = min x.length y.length := by simp [Spec.Cbc.xor]

section
variable {bw : Nat} {ciph : Cipher} (hc : ∀ b, (ciph b).length = 4 * bw)
include hc

theorem cbcEnc_computes : Computes (Mode.cbcEnc bw) (4 * bw) ciph (cbcEncF ciph) := by
  intro a
  have hb : rd (applyOps (Mode.cbcEnc bw).pre a) .buf (4 * bw) = xor (rd a .dat (4 * bw)) (rd a .chn (4 * bw)) :=
    rd_eq (by simp [xor_length, rd_length]) fun i hi => by
      simp only [Mode.cbcEnc, xorBlk_apply, true_and, hi, ite_true]
      rw [getD_xor (by simpa [rd_length]) (by simpa [rd_length]), getD_rd hi, getD_rd hi]
  simp only [stepA, Mode.cbcEnc, cbcEncF, applyOps_append] at hb ⊢
  refine ⟨rd_eq (hc _) fun i hi => ?_, rd_eq (hc _) fun i hi => ?_⟩
  · rw [copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩, copyBlk_apply (by decide), ite_eq_right (by simp)]
    simp only [cryptBuf, ite_true, hb]
  · rw [copyBlk_apply (by decide), ite_eq_right (by simp), copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
    simp only [cryptBuf, ite_true, hb]

theorem cbcDec_computes : Computes (Mode.cbcDec bw) (4 * bw) ciph (cbcDecF ciph) := by
  intro a
  have hb : rd (applyOps (Mode.cbcDec bw).pre a) .buf (4 * bw) = rd a .dat (4 * bw) :=
    rd_eq (by simp [rd_length]) fun i hi => by
      simp only [Mode.cbcDec, copyBlk_apply (show Loc.buf ≠ .dat by decide), true_and, hi, ite_true]
      rw [getD_rd hi]
  simp only [stepA, Mode.cbcDec, cbcDecF, applyOps_append] at hb ⊢
  refine ⟨rd_eq (by simp [xor_length, hc, rd_length]) fun i hi => ?_, rd_eq (rd_length _ _ _) fun i hi => ?_⟩
  · rw [copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩, copyBlk_apply (by decide), ite_eq_right (by simp),
      xorBlk_apply, ite_eq_left ⟨rfl, hi⟩]
    simp only [cryptBuf, ite_true, hb]
    have h1 : ∀ (l : Loc), ¬ (l = Loc.buf) → applyOps (copyBlk bw .buf .dat) a l = a l := fun l hl => by
      funext j; rw [copyBlk_apply (by decide), ite_eq_right (fun h => hl h.1)]
    rw [ite_eq_right (by simp), h1 .chn (by decide), getD_xor (by rw [hc]; exact hi) (by rw [rd_length]; exact hi),
      getD_rd hi]
  · rw [copyBlk_apply (by decide), ite_eq_right (by simp), copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩,
      xorBlk_apply, ite_eq_right (by simp)]
    simp only [cryptBuf, ite_eq_right (show Loc.dat ≠ Loc.buf by decide)]
    rw [copyBlk_apply (by decide), ite_eq_right (fun h => nomatch h.1), getD_rd hi]

theorem ofb_computes : Computes (Mode.ofb bw) (4 * bw) ciph (ofbF ciph) := by
  intro a
  have hb : rd (applyOps (Mode.ofb bw).pre a) .buf (4 * bw) = rd a .chn (4 * bw) :=
    rd_eq (by simp [rd_length]) fun i hi => by
      simp only [Mode.ofb, copyBlk_apply (show Loc.buf ≠ .chn by decide), true_and, hi, ite_true]
      rw [getD_rd hi]
  simp only [stepA, Mode.ofb, ofbF, applyOps_append] at hb ⊢
  refine ⟨rd_eq (by simp [xor_length, hc, rd_length]) fun i hi => ?_, rd_eq (hc _) fun i hi => ?_⟩
  · rw [xorBlk_apply, ite_eq_left ⟨rfl, hi⟩, copyBlk_apply (by decide), ite_eq_right (by simp),
      copyBlk_apply (by decide), ite_eq_right (by simp)]
    simp only [cryptBuf, ite_true, hb, ite_eq_right (show Loc.dat ≠ Loc.buf by decide)]
    rw [copyBlk_apply (by decide), ite_eq_right (fun h => nomatch h.1),
      getD_xor (by rw [rd_length]; exact hi) (by rw [hc]; exact hi), getD_rd hi]
  · rw [xorBlk_apply, ite_eq_right (by simp), copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
    simp only [cryptBuf, ite_true, hb]

theorem cfbEnc_computes : Computes (Mode.cfbEnc bw) (4 * bw) ciph (cfbEncF ciph) := by
  intro a
  have hb : rd (applyOps (Mode.cfbEnc bw).pre a) .buf (4 * bw) = rd a .chn (4 * bw) :=
    rd_eq (by simp [rd_length]) fun i hi => by
      simp only [Mode.cfbEnc, copyBlk_apply (show Loc.buf ≠ .chn by decide), true_and, hi, ite_true]
      rw [getD_rd hi]
  have hd : ∀ i < 4 * bw, applyOps (xorBlk bw .dat .dat .buf)
      (cryptBuf (4 * bw) ciph (applyOps (copyBlk bw .buf .chn) a)) .dat i =
      (xor (rd a .dat (4 * bw)) (ciph (rd a .chn (4 * bw)))).getD i 0 := fun i hi => by
    rw [xorBlk_apply, ite_eq_left ⟨rfl, hi⟩]
    simp only [Mode.cfbEnc] at hb
    simp only [cryptBuf, ite_true, hb, ite_eq_right (show Loc.dat ≠ Loc.buf by decide)]
    rw [copyBlk_apply (by decide), ite_eq_right (fun h => nomatch h.1),
      getD_xor (by rw [rd_length]; exact hi) (by rw [hc]; exact hi), getD_rd hi]
  simp only [stepA, Mode.cfbEnc, cfbEncF, applyOps_append]
  have hl : (xor (rd a .dat (4 * bw)) (ciph (rd a .chn (4 * bw)))).length = 4 * bw := by
    simp [xor_length, hc, rd_length]
  refine ⟨rd_eq hl fun i hi => ?_, rd_eq hl fun i hi => ?_⟩
  · rw [copyBlk_apply (by decide), ite_eq_right (by simp), hd i hi]
  · rw [copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩, hd i hi]

theorem cfbDec_computes : Computes (Mode.cfbDec bw) (4 * bw) ciph (cfbDecF ciph) := by
  intro a
  have hb : rd (applyOps (Mode.cfbDec bw).pre a) .buf (4 * bw) = rd a .chn (4 * bw) :=
    rd_eq (by simp [rd_length]) fun i hi => by
      simp only [Mode.cfbDec, copyBlk_apply (show Loc.buf ≠ .chn by decide), true_and, hi, ite_true]
      rw [getD_rd hi]
  simp only [stepA, Mode.cfbDec, cfbDecF, applyOps_append] at hb ⊢
  have h0 : ∀ l, l ≠ Loc.buf → ∀ j, cryptBuf (4 * bw) ciph (applyOps (copyBlk bw .buf .chn) a) l j = a l j :=
    fun l hl j => by
      simp only [cryptBuf, ite_eq_right hl]
      rw [copyBlk_apply (by decide), ite_eq_right (fun h => hl h.1)]
  refine ⟨rd_eq (by simp [xor_length, hc, rd_length]) fun i hi => ?_, rd_eq (rd_length _ _ _) fun i hi => ?_⟩
  · rw [xorBlk_apply, ite_eq_left ⟨rfl, hi⟩, copyBlk_apply (by decide), ite_eq_right (by simp),
      copyBlk_apply (by decide), ite_eq_right (by simp), h0 _ (by decide)]
    simp only [cryptBuf, ite_true, hb]
    rw [getD_xor (by rw [rd_length]; exact hi) (by rw [hc]; exact hi), getD_rd hi]
  · rw [xorBlk_apply, ite_eq_right (by simp), copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩, h0 _ (by decide),
      getD_rd hi]

end

theorem headD_eq_getD (xs : List Byte) : xs.headD 0 = xs.getD 0 0 := by cases xs <;> rfl

theorem tail_snoc_getD {c : List Byte} {n : Nat} (hc : c.length = n) (y : Byte) {i : Nat} (hi : i < n) :
    (c.tail ++ [y]).getD i 0 = if i < n - 1 then c.getD (i + 1) 0 else y := by
  simp only [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by simp [hc]; omega), List.getElem?_tail]
  · rw [List.getElem?_append_right (by simp [hc]; omega)]
    simp [hc, show i - (n - 1) = 0 by omega]

/-- CFB8's byte XOR: `dat[0] := dat[0] ⊕ buf[0]`. -/
def xorByte : Op := { wide := false, dst := .dat, dOff := 0, src := .dat, sOff := 0, xr := some (.buf, 0) }

theorem xorByte_apply (a : Areas) (l : Loc) (i : Nat) :
    xorByte.apply a l i = if l = .dat ∧ i = 0 then a .dat 0 ^^^ a .buf 0 else a l i := by
  simp only [Op.apply, xorByte, Op.width, Op.val, Bool.false_eq_true, ite_false, Nat.zero_add]
  by_cases h : l = .dat ∧ i = 0
  · rw [ite_eq_left ⟨h.1, Nat.zero_le _, by omega⟩, ite_eq_left h, h.2]
  · rw [ite_eq_right (fun h' => h ⟨h'.1, by omega⟩), ite_eq_right h]

/-- After CFB8's `pre` and the block cipher: `buf` is `CIPH_K(I)`. -/
theorem cfb8_crypt {bw : Nat} {ciph : Cipher} (a : Areas) (l : Loc) (j : Nat) :
    cryptBuf (4 * bw) ciph (applyOps (copyBlk bw .buf .chn) a) l j =
      if l = .buf then (ciph (rd a .chn (4 * bw))).getD j 0 else a l j := by
  have hb : rd (applyOps (copyBlk bw .buf .chn) a) .buf (4 * bw) = rd a .chn (4 * bw) :=
    rd_eq (by simp [rd_length]) fun i hi => by
      simp only [copyBlk_apply (show Loc.buf ≠ .chn by decide), true_and, hi, ite_true]
      rw [getD_rd hi]
  simp only [cryptBuf, hb]
  split
  · rfl
  · rename_i hl; rw [copyBlk_apply (by decide), ite_eq_right (fun h => hl h.1)]

section
variable {bw : Nat} {ciph : Cipher} (hbw : 0 < bw)
include hbw

theorem cfb8Enc_computes : Computes (Mode.cfb8Enc bw) (4 * bw) ciph (cfb8EncF ciph) := by
  intro a
  have hy : ∀ l i, xorByte.apply (cryptBuf (4 * bw) ciph (applyOps (copyBlk bw .buf .chn) a)) l i =
      if l = .dat ∧ i = 0 then a .dat 0 ^^^ (ciph (rd a .chn (4 * bw))).getD 0 0
      else if l = .buf then (ciph (rd a .chn (4 * bw))).getD i 0 else a l i := fun l i => by
    rw [xorByte_apply]
    by_cases h : l = .dat ∧ i = 0
    · rw [ite_eq_left h, ite_eq_left h, cfb8_crypt, cfb8_crypt, ite_eq_right (by simp), ite_eq_left rfl]
    · rw [ite_eq_right h, ite_eq_right h, cfb8_crypt]
  have e : Mode.cfb8Enc bw = ⟨copyBlk bw .buf .chn, xorByte :: Mode.shiftIn bw, 1, true⟩ := rfl
  rw [e]
  simp only [stepA, cfb8EncF, applyOps_cons]
  refine ⟨rd_eq rfl fun i hi => ?_, rd_eq (by simp [rd_length]; omega) fun i hi => ?_⟩
  · have : i = 0 := by omega
    subst this
    rw [shiftIn_apply, ite_eq_right (fun h => nomatch h.1), ite_eq_right (fun h => nomatch h.1), hy,
      ite_eq_left ⟨rfl, rfl⟩]
    rw [List.getD_cons_zero, headD_eq_getD, headD_eq_getD, getD_rd (show 0 < 1 by omega)]
  · rw [shiftIn_apply, tail_snoc_getD (rd_length _ _ _) _ hi]
    by_cases h : i < 4 * bw - 1
    · rw [ite_eq_left ⟨rfl, h⟩, ite_eq_left h, hy, ite_eq_right (fun h => nomatch h.1), ite_eq_right (by simp),
        getD_rd (by omega)]
    · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right h, ite_eq_left ⟨rfl, by omega⟩, hy, ite_eq_left ⟨rfl, rfl⟩]
      rw [headD_eq_getD, headD_eq_getD, getD_rd (show 0 < 1 by omega)]

theorem cfb8Dec_computes : Computes (Mode.cfb8Dec bw) (4 * bw) ciph (cfb8DecF ciph) := by
  intro a
  have e : Mode.cfb8Dec bw = ⟨copyBlk bw .buf .chn, Mode.shiftIn bw ++ [xorByte], 1, true⟩ := rfl
  rw [e]
  simp only [stepA, cfb8DecF, applyOps_snoc]
  refine ⟨rd_eq rfl fun i hi => ?_, rd_eq (by simp [rd_length]; omega) fun i hi => ?_⟩
  · have : i = 0 := by omega
    subst this
    rw [xorByte_apply, ite_eq_left ⟨rfl, rfl⟩, shiftIn_apply, ite_eq_right (fun h => nomatch h.1),
      ite_eq_right (fun h => nomatch h.1), shiftIn_apply, ite_eq_right (fun h => nomatch h.1),
      ite_eq_right (fun h => nomatch h.1), cfb8_crypt, cfb8_crypt, ite_eq_right (by simp),
      ite_eq_left rfl]
    rw [List.getD_cons_zero, headD_eq_getD, headD_eq_getD, getD_rd (show 0 < 1 by omega)]
  · rw [xorByte_apply, ite_eq_right (fun h => nomatch h.1), shiftIn_apply, tail_snoc_getD (rd_length _ _ _) _ hi]
    by_cases h : i < 4 * bw - 1
    · rw [ite_eq_left ⟨rfl, h⟩, ite_eq_left h, cfb8_crypt, ite_eq_right (by simp), getD_rd (by omega)]
    · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right h, ite_eq_left ⟨rfl, by omega⟩, cfb8_crypt,
        ite_eq_right (by simp)]
      rw [headD_eq_getD, getD_rd (show 0 < 1 by omega)]

end

/-! ## Data in memory, in steps -/

/-- The `n` steps of `L` bytes at `p`. -/
def chunksAt (L : Nat) (m : Mem) (p : Addr) (n : Nat) : List (List Byte) :=
  (List.range n).map fun i => Spec.Aes.bytesAt m (p + BitVec.ofNat 64 (L * i)) L

theorem chunksAt_length (L : Nat) (m : Mem) (p : Addr) (n : Nat) : (chunksAt L m p n).length = n := by
  simp [chunksAt]

/-- The steps after a change of memory only in step `j`. -/
theorem chunksAt_set {m m' : Mem} {D : Addr} {L n j : Nat}
    (h : ∀ i < L * n, (i < L * j ∨ L * j + L ≤ i) → m' (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i)) :
    chunksAt L m' D n = (chunksAt L m D n).set j (Spec.Aes.bytesAt m' (D + BitVec.ofNat 64 (L * j)) L) := by
  apply List.ext_getElem (by simp [chunksAt])
  intro q h1 h2
  have hq : q < n := by simpa [chunksAt] using h1
  rw [List.getElem_set]
  split
  · rename_i e; subst e; simp [chunksAt]
  · rename_i hne
    simp only [chunksAt, List.getElem_map, List.getElem_range, Spec.Aes.bytesAt]
    refine List.map_congr_left fun u hu => ?_
    have hu := List.mem_range.mp hu
    have h3 : L * q + L ≤ L * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hq
    rw [VG.Offset.add_add]
    refine h _ (by omega) ?_
    rcases Nat.lt_or_gt_of_ne (Ne.symm hne) with hlt | hlt
    · left; have : L * q + L ≤ L * j := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega
    · right; have : L * j + L ≤ L * q := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      omega

/-- The outputs of the first `j` steps followed by the remaining inputs, after
step `j`. -/
theorem run_set (F : StepFn) (c : List Byte) {xs : List (List Byte)} {j : Nat} (hj : j < xs.length) :
    ((run F c (xs.take j)).1 ++ xs.drop j).set j (F (run F c (xs.take j)).2 xs[j]).1 =
      (run F c (xs.take (j + 1))).1 ++ xs.drop (j + 1) := by
  have hl : (run F c (xs.take j)).1.length = j := by rw [run_length, List.length_take]; omega
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, run_snoc,
    List.set_append_right _ _ (by omega), hl, Nat.sub_self, List.drop_eq_getElem_cons hj, List.set_cons_zero,
    List.append_assoc, List.singleton_append]

end VG.Proof.Modes
