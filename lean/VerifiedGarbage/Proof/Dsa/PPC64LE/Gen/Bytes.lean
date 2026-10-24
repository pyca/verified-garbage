module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Pieces
public import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: byte loops

`loop_nz`: a `do … while (r ≠ 0)` loop that runs its body `N` times.
`copyLoop_ok`: `copyBody`'s loop copies `n` bytes from `r3` to `r4`, which
are apart. `zeroLoop_ok`: `zeroN`'s loop zeroes `n` bytes from `r3`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A `do … while (r ≠ 0)` loop whose body runs `N` times: iteration `i`
keeps the invariant, and leaves `r` zero exactly when it is the last. -/
theorem loop_nz {body : Prog isa} {r : Reg} {Q : State → Prop} (Inv : Nat → State → Prop) {N : Nat}
    (hN : 0 < N)
    (hstep : ∀ i < N, ∀ s, Inv i s →
      WP isa body s (fun s' => Inv (i + 1) s' ∧ (s'.gpr r != 0) = decide (i + 1 ≠ N)))
    (hQ : ∀ s, Inv N s → Q s) {s₀ : State} (h0 : Inv 0 s₀) : WP isa (.loop body (.nonzero .d r)) s₀ Q := by
  let I : Nat → State → Prop := fun n s => ∃ i, i < N ∧ n = N - i ∧ Inv i s
  have hI : I N s₀ := ⟨0, hN, (Nat.sub_zero N).symm, h0⟩
  refine WP.loop (M := isa) (body := body) (c := .nonzero .d r) (Q := Q) I ?_ N s₀ hI
  rintro n s ⟨i, hi, rfl, hs⟩
  refine WP.mono (hstep i hi s hs) fun s' ⟨hs', hz⟩ => ?_
  have ev : isa.eval (.nonzero .d r) s' = some (decide (i + 1 ≠ N)) := by
    rw [eval_nonzero]; simpa using hz
  by_cases h : i + 1 = N
  · refine .inl ⟨by rw [ev]; simp [h], hQ s' (h ▸ hs')⟩
  · exact .inr ⟨by rw [ev]; simp [h], N - (i + 1), by omega, i + 1, by omega, rfl, hs'⟩

/-- The count after `subi r, r, 1` from `N - i`. -/
theorem count_sub {N i : Nat} (hi : i < N) :
    BitVec.ofNat 64 (N - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (N - (i + 1)) := by
  rw [show N - i = (N - (i + 1)) + 1 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]

/-- The count is nonzero exactly when it is not the last iteration. -/
theorem count_nz {N i : Nat} (hi : i < N) (hN : N < 2 ^ 64) :
    (BitVec.ofNat 64 (N - (i + 1)) != 0) = decide (i + 1 ≠ N) := by
  by_cases h : i + 1 = N
  · subst h; simp
  · have h1 : (BitVec.ofNat 64 (N - (i + 1))).toNat = N - (i + 1) := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have : BitVec.ofNat 64 (N - (i + 1)) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e; rw [h1] at this; simp at this; omega
    rw [bne_iff_ne.mpr this]; simp [h]

theorem ptr_succ1 (p : BitVec 64) (i : Nat) :
    p + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## Copies -/

/-- After copying `k` bytes of `len` from `S` to `D`. -/
structure CopyInv (S D : Addr) (len : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = S + BitVec.ofNat 64 k
  r4 : s.gpr .r4 = D + BitVec.ofNat 64 k
  r5 : s.gpr .r5 = BitVec.ofNat 64 (len - k)
  keep : Keep [.r3, .r4, .r5, .r6] s₀ s
  sp : s.sp = s₀.sp
  frame : Frame [⟨D, len⟩] s₀.mem s.mem
  bytes : ∀ t < k, s.mem (D + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t)

theorem copy_step {S D : Addr} {len : Nat} {s₀ : State} (hlen : len < 2 ^ 64)
    (hd : (⟨S, len⟩ : Region).Disjoint ⟨D, len⟩)
    (cr : ∀ k < len, InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 k) 1)
    (cw : ∀ k < len, InRegions s₀.wr (D + BitVec.ofNat 64 k) 1)
    {k : Nat} (hk : k < len) {s : State} (h : CopyInv S D len s₀ k s) :
    WP isa (.block VG.Impl.MlKem.PPC64LE.copyBody) s fun s' =>
      CopyInv S D len s₀ (k + 1) s' ∧ (s'.gpr .r5 != 0) = decide (k + 1 ≠ len) := by
  have cS : (⟨S, len⟩ : Region).Contains (S + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  have cD : (⟨D, len⟩ : Region).Contains (D + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  refine WP.sp_eq ?_
  simp only [VG.Impl.MlKem.PPC64LE.copyBody]
  refine wp_lbz (by decide) (by decide) (by rw [h.r3, BitVec.add_zero]) (by rw [h.keep.2.1, h.keep.2.2]; exact cr k hk)
    fun s₁ u₁ => ?_
  refine wp_stb (by decide) (by decide) (by rw [u₁.other _ (by decide), h.r4, BitVec.add_zero])
    (by rw [u₁.wr, h.keep.2.2]; exact cw k hk) fun s₂ m₂ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun s₃ u₃ sp₃ _ => ?_
  refine WP.wr (exec_addi (by decide) (by decide)) fun s₄ u₄ sp₄ _ => ?_
  refine WP.wr (exec_subi (by decide) (by decide)) fun s₅ u₅ sp₅ _ => WP.block_nil fun sp => ⟨⟨?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, m₂.gpr, u₁.other _ (by decide), h.r3, ptr_succ1]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r4, ptr_succ1]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r5,
      count_sub hk]
  · refine ⟨fun r hr => ?_, by rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd, h.keep.2.1],
      by rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, h.keep.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.2.1, u₄.other _ hr.2.1, u₃.other _ hr.1, m₂.gpr, u₁.other _ hr.2.2.2,
      h.keep.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  · rw [sp, h.sp]
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ cD
  · intro t ht
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem, write1_apply, u₁.gpr, setWidth8_64]
    by_cases e : t = k
    · subst e
      rw [ite_eq_left (by simp)]
      exact h.frame _ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd _ cS
    · have hne : ¬ ((D + BitVec.ofNat 64 t - (D + BitVec.ofNat 64 k)).toNat < 1) := by
        intro hlt
        have e0 : D + BitVec.ofNat 64 t - (D + BitVec.ofNat 64 k) = 0 :=
          BitVec.eq_of_toNat_eq (by have : (0 : BitVec 64).toNat = 0 := rfl; omega)
        apply Offset.add_ofNat_ne D (a := t) (b := k) (by omega) (by omega) e
        rw [← BitVec.sub_add_cancel (D + BitVec.ofNat 64 t) (D + BitVec.ofNat 64 k), e0]; simp
      rw [ite_eq_right hne]; exact h.bytes t (by omega)
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), h.r5,
      count_sub hk]
    exact count_nz hk hlen

/-- `len > 0` bytes copied from `S` to `D`, with the pointers and the count in
`r3`–`r5`. -/
theorem copyLoop_ok {S D : Addr} {len : Nat} {s₀ : State} (hlen : len < 2 ^ 64) (hl0 : 0 < len)
    (hd : (⟨S, len⟩ : Region).Disjoint ⟨D, len⟩)
    (cr : ∀ k < len, InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 k) 1)
    (cw : ∀ k < len, InRegions s₀.wr (D + BitVec.ofNat 64 k) 1)
    (h3 : s₀.gpr .r3 = S) (h4 : s₀.gpr .r4 = D) (h5 : s₀.gpr .r5 = BitVec.ofNat 64 len) :
    WP isa (.loop (.block VG.Impl.MlKem.PPC64LE.copyBody) (.nonzero .d .r5)) s₀ fun s =>
      Keep [.r3, .r4, .r5, .r6] s₀ s ∧ s.sp = s₀.sp ∧ Frame [⟨D, len⟩] s₀.mem s.mem ∧
      Spec.Rsa.bytesAt s.mem D len = Spec.Rsa.bytesAt s₀.mem S len :=
  loop_nz (CopyInv S D len s₀) hl0 (fun k hk s h => copy_step hlen hd cr cw hk h)
    (fun s h => ⟨h.keep, h.sp, h.frame, by
      simp only [Spec.Rsa.bytesAt]
      exact List.map_congr_left fun t ht => h.bytes t (List.mem_range.mp ht)⟩)
    ⟨by rw [h3]; simp, by rw [h4]; simp, by rw [h5]; simp, Keep.refl _ _, rfl, Frame.refl _ _,
      fun t ht => absurd ht (Nat.not_lt_zero t)⟩

/-! ## Copies as pieces -/

theorem GP.sa_add (G : GP) (o i : Nat) : G.sa o + BitVec.ofNat 64 i = G.sa (o + i) := by
  simp only [GP.sa, BitVec.add_assoc, ← BitVec.ofNat_add]

open GP (sa_add) in

section
variable {G : GP} {STK : Nat}

/-- A copy between two ranges of `scratch` past the header, apart from the key
working space and from each other: the claims `cl'` apart from the
destination kept, the destination's bytes those of the source. -/
theorem copyS_vp {F Q : State → State → Prop} {c : State → Cfg} {dst src n : Nat}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) (hn : 0 < n) (hn15 : n < 2 ^ 15) (hd15 : dst < 2 ^ 15)
    (hs15 : src < 2 ^ 15) (hdo : ∀ σ s, F σ s → ClOk G (dst, List.replicate n 0))
    (hso : ∀ σ s, F σ s → src + n ≤ G.scrLen * 8)
    (hsep : dst + n ≤ src ∨ src + n ≤ dst)
    (k : ∀ σ s t, F σ s → SS G STK σ { c σ with cl := (c σ).cl.filter fun x => decide (Apart dst n x) } t →
      Keep [.r3, .r4, .r5, .r6] s t →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem (G.sa src) n → Q σ t) :
    VP F (copyS dst src n) Q := by
  refine VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (copyS 512 576 8), rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s hs => ?_
  have h := hF σ s hs
  have gi := h.gi
  have fit := gi.scrFit
  obtain ⟨dE, dK, dS⟩ := hdo σ s hs
  simp only [List.length_replicate] at dK dS
  have sS := hso σ s hs
  refine WP.sp_eq ?_
  simp only [copyS, copyN, List.cons_append, List.nil_append]
  refine WP.seq ?_
  refine WP.wr (exec_addi (by decide) hs15) fun s₁ u₁ _ _ => ?_
  refine WP.wr (exec_addi (by decide) hd15) fun s₂ u₂ _ _ => ?_
  refine WP.wr (exec_li hn15) fun s₃ u₃ _ _ => WP.block_nil ?_
  have r28 : s.gpr .r28 = G.scr := gi.r28
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (copyLoop_ok (S := G.sa src) (D := G.sa dst) (by omega) hn
    (gi.sdisj hsep.symm (by omega) (by omega))
    (fun i hi => by rw [rd₃, wr₃, sa_add]; exact gi.inRdWr (o := src + i) (n := 1) (by omega))
    (fun i hi => by rw [wr₃, sa_add]; exact gi.inScr (o := dst + i) (n := 1) (by omega))
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, r28])
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), r28]) (by rw [u₃.gpr]))
    fun t ⟨kp, sp', f, b⟩ sp => ?_
  have K : Keep [.r3, .r4, .r5, .r6] s t := by
    refine ⟨fun r hr => ?_, by rw [kp.2.1, rd₃], by rw [kp.2.2, wr₃]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kp.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), u₃.other _ hr.2.2.1, u₂.other _ hr.2.1,
      u₁.other _ hr.1]
  refine k σ s t hs ?_ K (by rw [b, m₃])
  refine h.of_scrs (os := [(dst, n)]) K sp (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact ⟨dE, by simpa using dK, by simpa using dS⟩)
    (by rw [← m₃]; exact f.mono fun r hr => by simp at hr ⊢; exact .inl hr) fun x hx => .inl ?_
  obtain ⟨hm, ha⟩ := List.mem_filter.mp hx
  exact ⟨hm, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; simpa using ha⟩

/-- A copy of `n` bytes from the pointer `P` in the header word `o` (to a
region apart from `scratch` and the stack below the stack pointer, readable)
to a range of `scratch` past the header, apart from the key working space:
the claims `cl'` apart from the destination kept, the destination's bytes
those at `P`. -/
theorem copyIn_vp {F Q : State → State → Prop} {c : State → Cfg} {o dst n : Nat} {P : Addr}
    (hF : ∀ σ s, F σ s → SS G STK σ (c σ) s) (hn : 0 < n) (hn15 : n < 2 ^ 15) (hd15 : dst < 2 ^ 15)
    (ho : o + 8 ≤ hEnd) (h8 : o % 8 = 0) (hP : ∀ σ s, F σ s → fw s.mem G o = P)
    (hdo : ∀ σ s, F σ s → ClOk G (dst, List.replicate n 0))
    (hPr : ∀ σ s, F σ s → InRegions (s.rd ++ s.wr) P n ∧ P.toNat + n ≤ 2 ^ 64 ∧
      (⟨P, n⟩ : Region).Disjoint G.rScr)
    (k : ∀ σ s t, F σ s → SS G STK σ { c σ with cl := (c σ).cl.filter fun x => decide (Apart dst n x) } t →
      Keep [.r3, .r4, .r5, .r6] s t →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem P n → Q σ t) :
    VP F (copyN [ld .r3 o] [scr .r4 dst] n) Q := by
  let M : State → State → Prop := fun σ t => ∃ s, F σ s ∧ SS G STK σ (c σ) t ∧ Keep [.r3, .r4, .r5] s t ∧
    t.sp = s.sp ∧ t.mem = s.mem ∧ t.gpr .r3 = P ∧ t.gpr .r4 = G.sa dst ∧ t.gpr .r5 = BitVec.ofNat 64 n
  refine VP.seq (G := M) (VP.pub (SS.pub hF) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28])
    (.block ([ld .r3 o] ++ [scr .r4 dst] ++ [.li .r5 n])), rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s hs => ?_) (VP.pub (G := G) (fun σ t ⟨_, _, h, _⟩ => ⟨h.gi.r28, by
      rw [h.gi.sp, ← h.gi.hG]; rfl⟩) [.r3, .r4, .r5] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
      (Taint.ofRegs [.r28, .r3, .r4, .r5]) (.loop (.block VG.Impl.MlKem.PPC64LE.copyBody) (.nonzero .d .r5)), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ ⟨_, _, _, _, _, _, a3, a4, a5⟩ ⟨_, _, _, _, _, _, b3, b4, b5⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a3, b3]
      · rw [a4, b4]
      · rw [a5, b5]) fun σ t ⟨s, hs, h, K₁, sp₁, m₁, t3, t4, t5⟩ => ?_)
  · have h := hF σ s hs
    have hE := h.gi.hEnd_le
    simp only [List.cons_append, List.nil_append]
    refine WP.cons (s' := s.write .r3 P) ?_ ?_
    · rw [show ld .r3 o = .load .d .r3 .r28 o from rfl, exec_load_d (by decide)
        ⟨by simp only [hEnd, fSave] at ho; omega, by omega⟩ (by rw [h.gi.r28]; exact h.gi.inRdWr (by omega)),
        h.gi.r28, ← hP σ s hs]
    have u₁ : Upd s (s.write .r3 P) .r3 P := Upd.write _ _ _
    refine WP.wr (exec_addi (by decide) hd15) fun s₂ u₂ sp₂ _ => ?_
    refine WP.wr (exec_li hn15) fun s₃ u₃ sp₃ _ => WP.block_nil ⟨s, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((h.of_upd u₁ rfl (by decide)).of_upd u₂ sp₂ (by decide)).of_upd u₃ sp₃ (by decide)
    · refine ⟨fun r hr => ?_, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]
    · rw [sp₃, sp₂]; rfl
    · rw [u₃.mem, u₂.mem, u₁.mem]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.gi.r28]
    · rw [u₃.gpr]
  have h₀ := hF σ s hs
  have gi := h₀.gi
  have fit := gi.scrFit
  obtain ⟨dE, dK, dS⟩ := hdo σ s hs
  simp only [List.length_replicate] at dK dS
  obtain ⟨Pr, Pf, Pd⟩ := hPr σ s hs
  have dsub : Region.Sub (G.rs dst n) G.rScr := sw G dS
  refine WP.sp_eq (WP.mono (copyLoop_ok (S := P) (D := G.sa dst) (by omega) hn (Pd.sub_right dsub)
    (fun i hi => ?_) (fun i hi => by rw [K₁.2.2, sa_add]; exact gi.inScr (o := dst + i) (n := 1) (by omega))
    t3 t4 t5) fun u ⟨kp, sp', f, b⟩ sp => ?_)
  · rw [K₁.2.1, K₁.2.2]
    obtain ⟨r, hr, hc⟩ := Pr
    have hb : (P + BitVec.ofNat 64 i - P).toNat < n := by
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi
    exact ⟨r, hr, hc.byte hb⟩
  have K : Keep [.r3, .r4, .r5, .r6] s u := by
    refine ⟨fun r hr => ?_, by rw [kp.2.1, K₁.2.1], by rw [kp.2.2, K₁.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kp.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), K₁.1 r (by simp [hr.1, hr.2.1, hr.2.2.1])]
  refine k σ s u hs ?_ K (by rw [b, m₁])
  refine h₀.of_scrs (os := [(dst, n)]) K (sp.trans sp₁) (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact ⟨dE, by simpa using dK, by simpa using dS⟩)
    (by rw [← m₁]; exact f.mono fun r hr => by simp at hr ⊢; exact .inl hr) fun x hx => .inl ?_
  obtain ⟨hm, ha⟩ := List.mem_filter.mp hx
  exact ⟨hm, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; simpa using ha⟩

end

end VG.Proof.Dsa.PPC64LE.Gen
