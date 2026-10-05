import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncCall

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: the mask

After the call, `out` and the result are masked by the zero test of `PS`
(`maskArgs_run`, `maskLoop_ok`), and `EM` is overwritten with zeros: `out`
then holds `encrypt`'s result, whatever `PS` held (`tail_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.WriteBytes (writeW8_apply)

/-- The mask: all ones if `PS` has no zero byte, zero if it has one. -/
def pmask (ok : Bool) : BitVec 64 := if ok then BitVec.allOnes 64 else 0

/-- Whether `PS` has no zero byte. -/
abbrev psOk (s : State) : Bool := (psB s).all (· != 0)

theorem not_zmask (bs : List Byte) :
    zmask bs ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = pmask (bs.all (· != 0)) := by
  unfold zmask pmask
  split <;> decide

theorem maskArgs_run {s t : State} (hp : EPre s) (h : PostCall s t) :
    WP isa (.block maskArgs) t fun t' => t'.mem = t.mem ∧ t'.gpr .rdx = pmask (psOk s) ∧
      t'.gpr .r11 = t.gpr .rax &&& pmask (psOk s) ∧ t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rcx = s.gpr .rcx ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ Keep [.rdx, .rax, .r11, .rdi, .rcx, .r10] t t' := by
  have hF := fb_toNat hp
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  refine WP.mono (WP.keep [.rdx, .rax, .r11, .rdi, .rcx, .r10] (c := .block maskArgs) (Q := fun t' =>
      t'.mem = t.mem ∧ t'.gpr .rdx = pmask (psOk s) ∧ t'.gpr .r11 = t.gpr .rax &&& pmask (psOk s) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r10 = BitVec.ofNat 64 0) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, k⟩
  xrun [maskArgs, ea_sp, h.rsp, hs.ld (d := oZ) (by decide), hs.ld (d := oOut) (by decide),
    hs.ld (d := oK) (by decide), h.sZ, h.slots.sOut, h.slots.sK, not_zmask]
  done

theorem low_and_pmask (b : Byte) (ok : Bool) :
    (BitVec.setWidth 64 b &&& pmask ok).setWidth 8 = if ok then b else 0 := by
  unfold pmask
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact BitVec.eq_of_toNat_eq (by simp)
  · simp only [↓reduceIte, BitVec.and_allOnes]; exact trunc_zext b

/-- After `j` bytes of the mask. -/
structure MaskInv (t₀ : State) (op Eb : Addr) (ok : Bool) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r10] t₀ t
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  out : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = if ok then t₀.mem (op + BitVec.ofNat 64 i) else 0
  em : ∀ i < j, t.mem (Eb + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → (∀ i < j, x ≠ Eb + BitVec.ofNat 64 i) → t.mem x = t₀.mem x

theorem maskLoop_ok {t : State} {S op : Addr} {k : Nat} {ok : Bool} (hk1 : 1 ≤ k) (hk : k < 2 ^ 63)
    (hsp : t.gpr .rsp = S) (hdi : t.gpr .rdi = op) (hdx : t.gpr .rdx = pmask ok)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 k) (h10 : t.gpr .r10 = BitVec.ofNat 64 0)
    (hwo : ∀ i < k, InRegions t.wr (op + BitVec.ofNat 64 i) 1)
    (hwm : ∀ i < k, InRegions t.wr (off S oEM + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < k, ∀ i' < k, op + BitVec.ofNat 64 i ≠ off S oEM + BitVec.ofNat 64 i') :
    WP isa maskLoop t fun t' => MaskInv t op (off S oEM) ok k t' := by
  refine wp_upto (a := 0) (N := k) (by omega) (MaskInv t op (off S oEM) ok) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, h10, fun _ h => absurd h (by omega), fun _ h => absurd h (by omega), fun _ _ _ => rfl⟩
  intro j _ hj u hI
  have hsp' : u.gpr .rsp = S := (hI.keep.gpr (by decide)).trans hsp
  have hdi' : u.gpr .rdi = op := (hI.keep.gpr (by decide)).trans hdi
  have hdx' : u.gpr .rdx = pmask ok := (hI.keep.gpr (by decide)).trans hdx
  have hcx' : u.gpr .rcx = BitVec.ofNat 64 k := (hI.keep.gpr (by decide)).trans hcx
  have hoj : InRegions u.wr (off op (0 + j)) 1 := by rw [hI.keep.2.2, Nat.zero_add]; exact hwo j hj
  have hoj' : InRegions (u.rd ++ u.wr) (off op (0 + j)) 1 :=
    let ⟨r, hr, hc⟩ := hoj; ⟨r, List.mem_append_right _ hr, hc⟩
  have hmj : InRegions u.wr (off S (oEM + j)) 1 := by rw [hI.keep.2.2, ← off_add]; exact hwm j hj
  have hb : u.mem (off op (0 + j)) = t.mem (op + BitVec.ofNat 64 j) := by
    rw [Nat.zero_add]
    exact hI.frame _ (fun i hi h => Offset.add_ofNat_ne op (by omega) (by omega) (show j ≠ i by omega) h)
      (fun i hi h => hsep j hj i (by omega) h)
  refine WP.mono (WP.keep [.rax, .r10] (Q := fun u' =>
      u'.mem = (u.mem.writeW (op + BitVec.ofNat 64 j)
        (if ok then t.mem (op + BitVec.ofNat 64 j) else 0)).writeW (off S oEM + BitVec.ofNat 64 j) (0 : Byte) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = k))) (by
    xrun [maskLoop, ea_bx (j := j) (p := op), ea_bx (j := j) (p := S), hsp', hdi', hI.r10, hdx', hcx',
      hoj, hoj', hmj, hb, low_and_pmask, ofNat_add_one, zero_trunc,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show k < 2 ^ 64 by omega)]
    rw [off_add, Nat.zero_add]) rfl) fun u' ⟨⟨hm, h10', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), h10', ?_, ?_, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply, writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (hsep i (by omega) j hj)),
        ite_eq_right_of_eq_false _ _ (eq_false (Offset.add_ofNat_ne op (by omega) (by omega) (show i ≠ j by omega)))]
      exact hI.out i hi
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (hsep i (by omega) i (by omega)))]; simp only [↓reduceIte]
  · intro i hi
    rw [hm, writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (Offset.add_ofNat_ne (off S oEM) (by omega) (by omega)
        (show i ≠ j by omega))), writeW8_apply,
        ite_eq_right_of_eq_false _ _ (eq_false fun h => hsep j hj i (by omega) h.symm)]
      exact hI.em i hi
    · simp only [↓reduceIte]
  · intro x hx hx'
    rw [hm, writeW8_apply, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx' j (by omega))),
      ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x (fun i hi => hx i (by omega)) fun i hi => hx' i (by omega)

theorem contains_of_byte {r : Region} {p : Addr} {n : Nat} (h : r = ⟨p, n⟩) (hn : n ≤ 2 ^ 64) {i : Nat}
    (hi : i < n) : r.Contains (p + BitVec.ofNat 64 i) 1 := by
  subst h; exact Offset.contains_base _ (by omega) (by omega)

/-- What the function's tail leaves, from the state after the call. -/
structure Tail (s t₀ t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame [stkR s, outR s, scrR s] s.mem t.mem
  rax : t.gpr .rax = t₀.gpr .rax &&& pmask (psOk s)
  out : Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (kOf s) =
    if psOk s then Spec.Rsa.bytesAt t₀.mem (s.gpr .rdi) (kOf s) else List.replicate (kOf s) 0
  keep : Keep [.rdx, .rax, .r11, .rdi, .rcx, .r10] t₀ t

theorem tail_ok {s t : State} (hp : EPre s) (h : PostCall s t) :
    WP isa (.seq (.block maskArgs) (.seq maskLoop (.block [.mov .rax (.reg .r11)]))) t (Tail s t) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsi := hp.hsi
  have hF := fb_toNat hp
  have e6 : oEM = 80 := rfl
  have e7 : frameBytes = 1112 := rfl
  have wO : (s.gpr .rcx).toNat ≤ 2 ^ 64 := by omega
  have hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by rw [h.wr, hp.hwr, ← hsi]; simp
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self ..
  refine WP.seq (WP.mono (maskArgs_run hp h) fun t₁ ⟨hm₁, hdx, h11, hdi, hcx, h10, k₁⟩ => ?_)
  have hsep : ∀ i < (s.gpr .rcx).toNat, ∀ i' < (s.gpr .rcx).toNat,
      s.gpr .rdi + BitVec.ofNat 64 i ≠ off (fb s) oEM + BitVec.ofNat 64 i' := fun i hi i' hi' he => by
    have hc := contains_of_byte (r := ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩) rfl wO hi'
    rw [← he] at hc
    have := hp.dKo; rw [hsi] at this
    exact (this.sub_left (frame_sub s (by omega))) _ hc (contains_of_byte rfl wO hi)
  refine WP.seq (WP.mono (maskLoop_ok (k := (s.gpr .rcx).toNat) (S := fb s) (by omega) (by omega)
    ((k₁.gpr (by decide)).trans h.rsp) hdi hdx (by rw [hcx]; simp) h10
    (fun i hi => ⟨_, by rw [k₁.2.2]; exact hout, contains_of_byte rfl wO hi⟩)
    (fun i hi => ⟨_, by rw [k₁.2.2]; exact hfr, by
      rw [off, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by omega) (by omega)⟩) hsep) fun t₂ hR => ?_)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.gpr .rax = t₂.gpr .r11 ∧ t'.mem = t₂.mem) (by xrun) rfl)
    fun t' ⟨⟨hax, hm⟩, k'⟩ => ?_
  have k13 := (k₁.trans hR.keep).trans k'
  refine ⟨(k13.gpr (by decide)).trans h.rsp, k13.2.1.trans h.rd, k13.2.2.trans h.wr, ?_,
    hax.trans ((hR.keep.gpr (by decide)).trans h11), ?_, k13.mono (by decide)⟩
  · refine frame_call h.mem (m₂ := t.mem) (rs := [outR s, ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩])
      (fun x hx => ?_) fun r hr => ?_
    · rw [hm, hR.frame x (fun i hi he => hx _ (List.mem_cons_self ..) (by
          rw [he, outR, hsi]; exact contains_of_byte rfl wO hi))
        (fun i hi he => hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by
          rw [he]; exact contains_of_byte rfl wO hi)), hm₁]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (.inl (sub_refl _))
      · exact .inl (frame_sub s (by omega))
  · rw [show kOf s = (s.gpr .rcx).toNat from rfl]
    split
    · rename_i hok
      simp only [Spec.Rsa.bytesAt, hm]
      exact List.map_congr_left fun i hi => by
        rw [hR.out i (List.mem_range.mp hi), hm₁]; simp only [hok, ↓reduceIte]
    · rename_i hok
      simp only [Spec.Rsa.bytesAt, hm]
      refine List.ext_getElem (by simp) fun i h₁ _ => ?_
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      rw [hR.out i (by simpa using h₁)]; simp only [hok, Bool.false_eq_true, ↓reduceIte]

end VG.Proof.RsaPkcs1Enc.X86_64
