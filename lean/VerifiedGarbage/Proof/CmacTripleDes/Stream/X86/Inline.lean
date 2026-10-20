module

import VerifiedGarbage.Proof.CmacTripleDes.X86.Init
import VerifiedGarbage.Proof.CmacTripleDes.X86.FinalizeCorrect
import VerifiedGarbage.Proof.CmacTripleDes.X86.CT
import VerifiedGarbage.Proof.CmacTripleDes.InlineCT
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86
public import VerifiedGarbage.Proof.CmacTripleDes.X86.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming TDEA-CMAC on x86: the code of `init`, `update` and `finalize`, inline

The code of `vg_cmac_triple_des_init`, `_update` and `_finalize` reads its
arguments from the stack: each run inside the streaming functions is in a
frame that pushes them, the last first, and one more word in the return
address's place (`WP.frameInline`, `RelCT.frameInline`), from its contract
(`WP.inline`). For each: what it needs (`…Args`: the registers pushed, and
the regions), what it leaves (`…Post`, in terms of the memory before it),
and that two runs with the same arguments and stack pointer leak the same
(`…_rel`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86
open VG.Proof.CmacTripleDes.X86 (updateX86 finalizeX86 initX86 ciphAt scheduleAt_frame)

/-! ## Inlining in a frame -/

/-- Argument `i` of code run in a frame pushing `rs`, the last of which is in
the return address's place: the `i + 2`-th register from the end. -/
theorem pushed_arg {rs : List Reg} {s : State} (hrs : Reg.esp ∉ rs) (hn : 4 * rs.length ≤ (s.gpr .esp).toNat)
    {i : Nat} (hi : i + 1 < rs.length) : arg (pushed rs s) i = s.gpr rs[rs.length - 1 - (i + 1)] := by
  have := pushed_word hrs hn (i := i + 1) hi
  show (pushed rs s).mem.readW (((pushed rs s).gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 32 = _
  rw [show 4 + 4 * i = 4 * (i + 1) by omega]
  exact this

theorem sub_add4 (x : BitVec 32) {a : Nat} (h : 4 ≤ a) (ha : a < 2 ^ 32) :
    x - BitVec.ofNat 32 a + BitVec.ofNat 32 4 = x - BitVec.ofNat 32 (a - 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- The first argument's address, in a frame of `rs`. -/
theorem pushed_argAddr0 {rs : List Reg} {s : State} {k : Nat} (hk : 4 * rs.length = k + 4) (hk' : k + 4 < 2 ^ 32) :
    argAddr (pushed rs s) 0 = (s.gpr .esp - BitVec.ofNat 32 k).setWidth 64 := by
  show ((pushed rs s).gpr .esp + BitVec.ofNat 32 4).setWidth 64 = _
  rw [pushed_esp, hk, sub_add4 _ (by omega) hk', Nat.add_sub_cancel]

/-- The `a` bytes just below `E`, in a region of the `b ≥ a` bytes below it. -/
theorem cov_below {E : BitVec 32} {a b : Nat} (hab : a ≤ b) (hb : b ≤ E.toNat) :
    Covers [⟨(E - BitVec.ofNat 32 a).setWidth 64, a⟩] [below E b] :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    refine ⟨below E b, List.mem_singleton_self _, b - a, ?_, by simp; omega⟩
    show (E - BitVec.ofNat 32 a).setWidth 64 = (E - BitVec.ofNat 32 b).setWidth 64 + BitVec.ofNat 64 (b - a)
    apply BitVec.eq_of_toNat_eq
    have := E.isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

/-- Verified code without calls, in the frame that pushes its arguments `rs`
(and a word in the return address's place), from its contract `k`: it runs
from the state after the push, with the permissions it is given; it leaves
the permissions and callee-saved registers of `s`, and changes memory only
within the regions it may write and the frame. -/
theorem WP.frameInline {rs : List Reg} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noCalls = true) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs) {s : State}
    (hd : 4 * rs.length ≤ (s.gpr .esp).toNat) {rd wr : List Region}
    (hpre : k.pre ((pushed rs s).withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ below (s.gpr .esp) (4 * rs.length) :: s.wr))
    (hw : Covers wr (below (s.gpr .esp) (4 * rs.length) :: s.wr)) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .esp) (4 * rs.length)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ k.post ((pushed rs s).withRegions rd wr) s₂) → Q s') :
    WP isa (.frame (.push rs) c (.pop .eax rs.length)) s Q := by
  refine WP.frame hne hrs (by decide) hd hsp ?_
  refine WP.inline (k := k) hv hpre (by rw [pushed_rd, pushed_wr]; exact hc) (by rw [pushed_wr]; exact hw)
    (fun s₂ rd₂ wr₂ ha f₂ _ post₂ => ?_) hn
  refine hQ _ (by rw [popped_rd, rd₂, pushed_rd]) (by rw [popped_wr, wr₂, pushed_wr]; rfl) (fun r hr => ?_) ?_
    ⟨s₂.withRegions rd wr, by rw [State.withRegions_mem, popped_mem], post₂⟩
  · by_cases h : r = .esp
    · subst h
      rw [popped_esp, ha.1 .esp hr, pushed_esp]; exact BitVec.sub_add_cancel _ _
    · have hne' : r ≠ .eax := by
        rintro rfl; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ h hne', ha.1 r hr, pushed_gpr _ _ h]
  · rw [popped_mem]
    exact ((pushed_frame hrs hd).mono fun r hr => List.mem_append_right _ hr).trans
      (f₂.mono fun r hr => List.mem_append_left _ hr)

/-- Two runs of such code leak the same if its contract holds in both, its
public data agree, and so does `esp`. -/
theorem RelCT.frameInline {rs : List Reg} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .esp = s₂.gpr .esp ∧
      k.pre ((pushed rs s₁).withRegions rd wr) ∧ k.pre ((pushed rs s₂).withRegions rd wr) ∧
      k.pub ((pushed rs s₁).withRegions rd wr) ((pushed rs s₂).withRegions rd wr) ∧
      Covers (rd ++ wr) (s₁.rd ++ below (s₁.gpr .esp) (4 * rs.length) :: s₁.wr) ∧
      Covers wr (below (s₁.gpr .esp) (4 * rs.length) :: s₁.wr) ∧
      Covers (rd ++ wr) (s₂.rd ++ below (s₂.gpr .esp) (4 * rs.length) :: s₂.wr) ∧
      Covers wr (below (s₂.gpr .esp) (4 * rs.length) :: s₂.wr)) :
    RelCT isa P (.frame (.push rs) c (.pop .eax rs.length)) fun _ _ => True := by
  refine VG.X86.RelCT.frame (R := fun _ _ => True) (fun s₁ s₂ h => (hP _ _ h).1) ?_
  refine relCT_inline regionModel (Post := fun s s' => abiPreserved s s' ∧ k.post s s') hv hct ?_
  rintro _ _ ⟨s₁, s₂, h, rfl, rfl⟩
  obtain ⟨-, p₁, p₂, q, c₁, w₁, c₂, w₂⟩ := hP _ _ h
  exact ⟨rd, wr, rd, wr, p₁, p₂, q,
    by show Covers _ ((pushed rs s₁).rd ++ (pushed rs s₁).wr); rw [pushed_rd, pushed_wr]; exact c₁,
    by show Covers _ (pushed rs s₁).wr; rw [pushed_wr]; exact w₁,
    by show Covers _ ((pushed rs s₂).rd ++ (pushed rs s₂).wr); rw [pushed_rd, pushed_wr]; exact c₂,
    by show Covers _ (pushed rs s₂).wr; rw [pushed_wr]; exact w₂⟩

theorem eq_ofNat {x : BitVec 32} {n : Nat} (h : x = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) : x.toNat = n := by
  rw [h, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn

/-- The bytes of a region the frame does not overlap, from the state the
frame is pushed in. -/
theorem keep_push {rs : List Reg} {s : State} (hrs : Reg.esp ∉ rs) (hd : 4 * rs.length ≤ (s.gpr .esp).toNat)
    {p : Addr} {n : Nat} (hb : (below (s.gpr .esp) (4 * rs.length)).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt (pushed rs s).mem p n = Spec.Aes.bytesAt s.mem p n :=
  Proof.Cmac.bytesAt_frame (pushed_frame hrs hd) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hb.symm) hn

/-- The return address's place and the arguments, in a frame of `b` bytes. -/
theorem ret_sub {E : BitVec 32} {b : Nat} (hb : 4 ≤ b) :
    Region.Sub ⟨(E - BitVec.ofNat 32 b).setWidth 64, 4⟩ (below E b) := Region.sub_prefix hb

theorem args_sub {E : BitVec 32} {b : Nat} (hb : 4 ≤ b) (he : b ≤ E.toNat) :
    Region.Sub ⟨(E - BitVec.ofNat 32 (b - 4)).setWidth 64, b - 4⟩ (below E b) := below_sub (by omega) he

theorem nosp_update : NoSp Impl.CmacTripleDes.X86.update := NoSp.of_all (by lit_decide)
theorem nosp_finalize : NoSp Impl.CmacTripleDes.X86.finalize := NoSp.of_all (by lit_decide)
theorem nosp_init : NoSp Impl.CmacTripleDes.X86.init := NoSp.of_all (by lit_decide)

/-! ## `update` -/

/-- The registers `updFrame` pushes. -/
abbrev rsU : List Reg := [.edi, .esi, .ebx, .edx, .eax, .ecx]

theorem hrsU : Reg.esp ∉ rsU := by decide

/-- What a run of `update` needs: the key schedule `W`, the chaining value
`C`, `n` blocks at `D` and the working space `S`, in `eax`, `edx`, `ebx`,
`esi` and `edi`. -/
structure UArgs (s : State) (W C D S : BitVec 32) (n : Nat) : Prop where
  eax : s.gpr .eax = W
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = D
  esi : s.gpr .esi = BitVec.ofNat 32 n
  edi : s.gpr .edi = S
  esp : 24 ≤ (s.gpr .esp).toNat
  hn : 8 * n < 2 ^ 32
  wc : (⟨W.setWidth 64, 384⟩ : Region).Disjoint ⟨C.setWidth 64, 8⟩
  ws : (⟨W.setWidth 64, 384⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  dc : (⟨D.setWidth 64, 8 * n⟩ : Region).Disjoint ⟨C.setWidth 64, 8⟩
  ds : (⟨D.setWidth 64, 8 * n⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  cs : (⟨C.setWidth 64, 8⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  bW : (below (s.gpr .esp) 24).Disjoint ⟨W.setWidth 64, 384⟩
  bD : (below (s.gpr .esp) 24).Disjoint ⟨D.setWidth 64, 8 * n⟩
  bC : (below (s.gpr .esp) 24).Disjoint ⟨C.setWidth 64, 8⟩
  bS : (below (s.gpr .esp) 24).Disjoint ⟨S.setWidth 64, 640⟩
  fW : W.toNat + 384 ≤ 2 ^ 32
  fC : C.toNat + 8 ≤ 2 ^ 32
  fD : D.toNat + 8 * n ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  reads : Covers [⟨W.setWidth 64, 384⟩, ⟨D.setWidth 64, 8 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨C.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩] s.wr

/-- What a run of `update` leaves. -/
structure UPost (s : State) (W C D S : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩, below (s.gpr .esp) 24] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (C.setWidth 64) 8 =
    Spec.Cmac.chain (ciphAt s.mem (W.setWidth 64)) (Spec.Aes.bytesAt s.mem (C.setWidth 64) 8)
      (Spec.Cmac.blocksAt s.mem (D.setWidth 64) 8 n)

/-- The regions the code of `update` runs with. -/
abbrev uRd (E W D : BitVec 32) (n : Nat) : List Region :=
  [⟨W.setWidth 64, 384⟩, ⟨D.setWidth 64, 8 * n⟩, ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
abbrev uWr (C S : BitVec 32) : List Region := [⟨C.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩]

/-- Covering a frame's regions, from those of the state it is pushed in. -/
theorem cov_frame {s : State} {rd₀ wr₀ : List Region} {a b : Nat} (hab : a ≤ b) (hb : b ≤ (s.gpr .esp).toNat)
    (hr : Covers rd₀ (s.rd ++ s.wr)) (hw : Covers wr₀ s.wr) :
    Covers ((rd₀ ++ [⟨(s.gpr .esp - BitVec.ofNat 32 a).setWidth 64, a⟩]) ++ wr₀)
      (s.rd ++ below (s.gpr .esp) b :: s.wr) := by
  intro x n ⟨r, hr', hcn⟩
  rcases List.mem_append.mp hr' with hr' | hr'
  · rcases List.mem_append.mp hr' with hr' | hr'
    · obtain ⟨r', hr'', hc'⟩ := hr x n ⟨r, hr', hcn⟩
      rcases List.mem_append.mp hr'' with h' | h'
      · exact ⟨r', List.mem_append_left _ h', hc'⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h'), hc'⟩
    · rw [List.mem_singleton] at hr'; subst hr'
      obtain ⟨r', hr'', hc'⟩ := cov_below hab hb x n ⟨_, List.mem_singleton_self _, hcn⟩
      rw [List.mem_singleton] at hr''; subst hr''
      exact ⟨_, List.mem_append_right _ List.mem_cons_self, hc'⟩
  · obtain ⟨r', hr'', hc'⟩ := hw x n ⟨r, hr', hcn⟩
    exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), hc'⟩

theorem covW_frame {s : State} {wr₀ : List Region} {b : Nat} (hw : Covers wr₀ s.wr) :
    Covers wr₀ (below (s.gpr .esp) b :: s.wr) := by
  intro x n hi
  obtain ⟨r', hr', hc'⟩ := hw x n hi
  exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

namespace UArgs
variable {s : State} {W C D S : BitVec 32} {n : Nat} (h : UArgs s W C D S n)
include h

theorem fit : 4 * rsU.length ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : arg (pushed rsU s) 0 = W ∧ arg (pushed rsU s) 1 = C ∧ arg (pushed rsU s) 2 = D ∧
    arg (pushed rsU s) 3 = BitVec.ofNat 32 n ∧ arg (pushed rsU s) 4 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [pushed_arg hrsU h.fit (by decide)] <;> simp [h.eax, h.edx, h.ebx, h.esi, h.edi]

theorem pre : updateX86.pre ((pushed rsU s).withRegions (uRd (s.gpr .esp) W D n) (uWr C S)) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h.args
  have hN : (BitVec.ofNat 32 n).toNat = n := eq_ofNat rfl (by have := h.hn; omega)
  have he := h.esp
  have eA : argAddr (pushed rsU s) 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := pushed_argAddr0 (k := 20) rfl (by decide)
  have eSp : (pushed rsU s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 := pushed_esp _ _
  have bA := args_sub (E := s.gpr .esp) (b := 24) (by decide) he
  have bR := ret_sub (E := s.gpr .esp) (b := 24) (by decide)
  simp only [updateX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, hN]
  refine ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.bC.sub_left bA, h.bS.sub_left bA,
    h.bC.sub_left bR, h.bS.sub_left bR, h.fW, h.fC, h.fD, h.fS, ?_⟩
  rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega

end UArgs

theorem upd_wp {s : State} {W C D S : BitVec 32} {n : Nat} (h : UArgs s W C D S n) :
    WP isa Impl.CmacTripleDes.Stream.X86.updFrame s (UPost s W C D S n) := by
  have hN : (BitVec.ofNat 32 n).toNat = n := eq_ofNat rfl (by have := h.hn; omega)
  refine WP.frameInline (rs := rsU) (k := updateX86) (fun _ hs => Proof.CmacTripleDes.X86.update_wp hs)
    (by lit_decide) nosp_update (by simp) hrsU h.fit h.pre (cov_frame (by decide) h.fit h.reads h.writes)
    (covW_frame h.writes) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, -⟩ := h.args
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  simp only [updateX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, hN, m₂] at post
  rw [post, ciphAt, ciphAt, scheduleAt_frame (pushed_frame hrsU h.fit) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bW.symm,
    keep_push hrsU h.fit h.bC (by decide)]
  congr 1
  simp only [Spec.Cmac.blocksAt]
  refine List.map_congr_left fun i hi => keep_push hrsU h.fit (h.bD.sub_right (Offset.sub_base _ ?_)) (by decide)
  rw [List.mem_range] at hi; omega

theorem upd_rel {W C D S E : BitVec 32} {n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S n ∧ UArgs s₂ W C D S n ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P Impl.CmacTripleDes.Stream.X86.updFrame fun _ _ => True := by
  refine RelCT.frameInline (rs := rsU) (fun _ hs => Proof.CmacTripleDes.X86.update_wp hs)
    Proof.CmacTripleDes.X86.update_ct (uRd E W D n) (uWr C S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [e₁] at p₁
  rw [e₂] at p₂
  have c₁ := cov_frame (s := s₁) (a := 20) (b := 24) (by decide) h₁.fit h₁.reads h₁.writes
  have c₂ := cov_frame (s := s₂) (a := 20) (b := 24) (by decide) h₂.fit h₂.reads h₂.writes
  obtain ⟨a0, a1, a2, a3, a4⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4⟩ := h₂.args
  refine ⟨e₁.trans e₂.symm, p₁, p₂, ⟨by simp only [State.withRegions_gpr, pushed_esp, e₁, e₂], fun i hi => ?_⟩,
    by subst e₁; exact c₁, covW_frame h₁.writes, by subst e₂; exact c₂, covW_frame h₂.writes⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

/-! ## `finalize` -/

/-- What a run of `finalize` needs: the key schedule and subkeys `K`, the
state `St`, the `L` last bytes at `P` and the working space `S`, in `eax`,
`edx`, `ebx`, `esi` and `edi`. -/
structure FArgs (s : State) (K St P S : BitVec 32) (L : Nat) : Prop where
  eax : s.gpr .eax = K
  edx : s.gpr .edx = St
  ebx : s.gpr .ebx = P
  esi : s.gpr .esi = BitVec.ofNat 32 L
  edi : s.gpr .edi = S
  len : L ≤ 8
  esp : 24 ≤ (s.gpr .esp).toNat
  kst : (⟨K.setWidth 64, 400⟩ : Region).Disjoint ⟨St.setWidth 64, 8⟩
  ks : (⟨K.setWidth 64, 400⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  pst : (⟨P.setWidth 64, L⟩ : Region).Disjoint ⟨St.setWidth 64, 8⟩
  ps : (⟨P.setWidth 64, L⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  sts : (⟨St.setWidth 64, 8⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  bK : (below (s.gpr .esp) 24).Disjoint ⟨K.setWidth 64, 400⟩
  bP : (below (s.gpr .esp) 24).Disjoint ⟨P.setWidth 64, L⟩
  bSt : (below (s.gpr .esp) 24).Disjoint ⟨St.setWidth 64, 8⟩
  bS : (below (s.gpr .esp) 24).Disjoint ⟨S.setWidth 64, 640⟩
  fK : K.toNat + 400 ≤ 2 ^ 32
  fSt : St.toNat + 8 ≤ 2 ^ 32
  fP : P.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  reads : Covers [⟨K.setWidth 64, 400⟩, ⟨P.setWidth 64, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨St.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩] s.wr

/-- What a run of `finalize` leaves. -/
structure FPost (s : State) (K St P S : BitVec 32) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩, below (s.gpr .esp) 24] s.mem s'.mem
  out : let ciph := ciphAt s.mem (K.setWidth 64)
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (K.setWidth 64 + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem (St.setWidth 64) 8 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem (St.setWidth 64) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem (P.setWidth 64) L)

/-- The regions the code of `finalize` runs with. -/
abbrev fRd (E K P : BitVec 32) (L : Nat) : List Region :=
  [⟨K.setWidth 64, 400⟩, ⟨P.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
abbrev fWr (St S : BitVec 32) : List Region := [⟨St.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩]

namespace FArgs
variable {s : State} {K St P S : BitVec 32} {L : Nat} (h : FArgs s K St P S L)
include h

theorem fit : 4 * rsU.length ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : arg (pushed rsU s) 0 = K ∧ arg (pushed rsU s) 1 = St ∧ arg (pushed rsU s) 2 = P ∧
    arg (pushed rsU s) 3 = BitVec.ofNat 32 L ∧ arg (pushed rsU s) 4 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [pushed_arg hrsU h.fit (by decide)] <;> simp [h.eax, h.edx, h.ebx, h.esi, h.edi]

theorem pre : finalizeX86.pre ((pushed rsU s).withRegions (fRd (s.gpr .esp) K P L) (fWr St S)) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h.args
  have hL : (BitVec.ofNat 32 L).toNat = L := eq_ofNat rfl (by have := h.len; omega)
  have he := h.esp
  have eA : argAddr (pushed rsU s) 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := pushed_argAddr0 (k := 20) rfl (by decide)
  have eSp : (pushed rsU s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 := pushed_esp _ _
  have bA := args_sub (E := s.gpr .esp) (b := 24) (by decide) he
  have bR := ret_sub (E := s.gpr .esp) (b := 24) (by decide)
  simp only [finalizeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, hL]
  refine ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.bSt.sub_left bA, h.bS.sub_left bA,
    h.bSt.sub_left bR, h.bS.sub_left bR, h.fK, h.fSt, h.fP, h.fS, ?_, h.len⟩
  rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega

end FArgs

theorem fin_wp {s : State} {K St P S : BitVec 32} {L : Nat} (h : FArgs s K St P S L) :
    WP isa Impl.CmacTripleDes.Stream.X86.finFrame s (FPost s K St P S L) := by
  have hL : (BitVec.ofNat 32 L).toNat = L := eq_ofNat rfl (by have := h.len; omega)
  refine WP.frameInline (rs := rsU) (k := finalizeX86) (fun _ hs => Proof.CmacTripleDes.X86.finalize_wp hs)
    (by lit_decide) nosp_finalize (by simp) hrsU h.fit h.pre (cov_frame (by decide) h.fit h.reads h.writes)
    (covW_frame h.writes) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, -⟩ := h.args
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  simp only [finalizeX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, hL, m₂] at post
  intro _ _ hk msg hm hne hst
  have hsch : ciphAt (pushed rsU s).mem (K.setWidth 64) = ciphAt s.mem (K.setWidth 64) := by
    simp only [ciphAt]
    rw [scheduleAt_frame (pushed_frame hrsU h.fit) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bK.sub_right (Region.sub_prefix (by decide))).symm]
  have eK2 := keep_push hrsU h.fit (p := K.setWidth 64 + 384) (n := 16)
    (h.bK.sub_right (Offset.sub_base (K.setWidth 64) (d := 384) (n := 16) (by decide))) (by decide)
  have eSt := keep_push hrsU h.fit h.bSt (by decide)
  have eP := keep_push hrsU h.fit h.bP (by have := h.len; omega)
  rw [hsch, eK2, eSt, eP] at post
  exact post hk msg hm hne hst

theorem fin_rel {K St P S E : BitVec 32} {L : Nat} {Q : State → State → Prop}
    (h : ∀ s₁ s₂, Q s₁ s₂ → FArgs s₁ K St P S L ∧ FArgs s₂ K St P S L ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa Q Impl.CmacTripleDes.Stream.X86.finFrame fun _ _ => True := by
  refine RelCT.frameInline (rs := rsU) (fun _ hs => Proof.CmacTripleDes.X86.finalize_wp hs)
    Proof.CmacTripleDes.X86.finalize_ct (fRd E K P L) (fWr St S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [e₁] at p₁
  rw [e₂] at p₂
  have c₁ := cov_frame (s := s₁) (a := 20) (b := 24) (by decide) h₁.fit h₁.reads h₁.writes
  have c₂ := cov_frame (s := s₂) (a := 20) (b := 24) (by decide) h₂.fit h₂.reads h₂.writes
  obtain ⟨a0, a1, a2, a3, a4⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4⟩ := h₂.args
  refine ⟨e₁.trans e₂.symm, p₁, p₂, ⟨by simp only [State.withRegions_gpr, pushed_esp, e₁, e₂], fun i hi => ?_⟩,
    by subst e₁; exact c₁, covW_frame h₁.writes, by subst e₂; exact c₂, covW_frame h₂.writes⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

/-! ## `init` -/

/-- The registers `initFrame` pushes. -/
abbrev rsI : List Reg := [.edx, .eax, .ecx, .ebx, .esi]

theorem hrsI : Reg.esp ∉ rsI := by decide

/-- What a run of `init` needs: the key `Kp` of `KL` bytes, the output `O` and
the working space `S`, in `ebx`, `ecx`, `eax` and `edx`. -/
structure IArgs (s : State) (Kp O S : BitVec 32) (KL : Nat) : Prop where
  ebx : s.gpr .ebx = Kp
  ecx : s.gpr .ecx = BitVec.ofNat 32 KL
  eax : s.gpr .eax = O
  edx : s.gpr .edx = S
  klen : Spec.TripleDes.validKey KL
  esp : 20 ≤ (s.gpr .esp).toNat
  ko : (⟨Kp.setWidth 64, KL⟩ : Region).Disjoint ⟨O.setWidth 64, 400⟩
  ks : (⟨Kp.setWidth 64, KL⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  os : (⟨O.setWidth 64, 400⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  bK : (below (s.gpr .esp) 20).Disjoint ⟨Kp.setWidth 64, KL⟩
  bO : (below (s.gpr .esp) 20).Disjoint ⟨O.setWidth 64, 400⟩
  bS : (below (s.gpr .esp) 20).Disjoint ⟨S.setWidth 64, 640⟩
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fO : O.toNat + 400 ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  reads : Covers [⟨Kp.setWidth 64, KL⟩] (s.rd ++ s.wr)
  writes : Covers [⟨O.setWidth 64, 400⟩, ⟨S.setWidth 64, 640⟩] s.wr

/-- What a run of `init` leaves. -/
structure IPost (s : State) (Kp O S : BitVec 32) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨O.setWidth 64, 400⟩, ⟨S.setWidth 64, 640⟩, below (s.gpr .esp) 20] s.mem s'.mem
  out : let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (Kp.setWidth 64) KL)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem (O.setWidth 64) = k ∧
      Spec.Aes.bytesAt s'.mem (O.setWidth 64 + 384) 16 = ks.1 ++ ks.2

/-- The regions the code of `init` runs with. -/
abbrev iRd (E Kp : BitVec 32) (KL : Nat) : List Region :=
  [⟨Kp.setWidth 64, KL⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩]
abbrev iWr (O S : BitVec 32) : List Region := [⟨O.setWidth 64, 400⟩, ⟨S.setWidth 64, 640⟩]

theorem cov_frameI {s : State} {Kp O S : BitVec 32} {KL : Nat} (hb : 20 ≤ (s.gpr .esp).toNat)
    (hr : Covers [⟨Kp.setWidth 64, KL⟩] (s.rd ++ s.wr)) (hw : Covers (iWr O S) s.wr) :
    Covers (iRd (s.gpr .esp) Kp KL ++ iWr O S) (s.rd ++ below (s.gpr .esp) 20 :: s.wr) :=
  cov_frame (rd₀ := [⟨Kp.setWidth 64, KL⟩]) (a := 16) (b := 20) (by decide) hb hr hw

namespace IArgs
variable {s : State} {Kp O S : BitVec 32} {KL : Nat} (h : IArgs s Kp O S KL)
include h

theorem fit : 4 * rsI.length ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : arg (pushed rsI s) 0 = Kp ∧ arg (pushed rsI s) 1 = BitVec.ofNat 32 KL ∧ arg (pushed rsI s) 2 = O ∧
    arg (pushed rsI s) 3 = S := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  rw [pushed_arg hrsI h.fit (by decide)] <;> simp [h.ebx, h.ecx, h.eax, h.edx]

theorem pre : initX86.pre ((pushed rsI s).withRegions (iRd (s.gpr .esp) Kp KL) (iWr O S)) := by
  obtain ⟨a0, a1, a2, a3⟩ := h.args
  have hK : (BitVec.ofNat 32 KL).toNat = KL := eq_ofNat rfl (by rcases h.klen with h | h <;> omega)
  have he := h.esp
  have eA : argAddr (pushed rsI s) 0 = (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := pushed_argAddr0 (k := 16) rfl (by decide)
  have eSp : (pushed rsI s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 := pushed_esp _ _
  have bA := args_sub (E := s.gpr .esp) (b := 20) (by decide) he
  have bR := ret_sub (E := s.gpr .esp) (b := 20) (by decide)
  simp only [initX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, hK]
  refine ⟨trivial, trivial, h.ko, h.ks, h.os, h.bO.sub_left bA, h.bS.sub_left bA,
    h.bO.sub_left bR, h.bS.sub_left bR, h.fK, h.fO, h.fS, ?_, h.klen⟩
  rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega

end IArgs

theorem init_inline_wp {s : State} {Kp O S : BitVec 32} {KL : Nat} (h : IArgs s Kp O S KL) :
    WP isa Impl.CmacTripleDes.Stream.X86.initFrame s (IPost s Kp O S KL) := by
  have hK : (BitVec.ofNat 32 KL).toNat = KL := eq_ofNat rfl (by rcases h.klen with h | h <;> omega)
  refine WP.frameInline (rs := rsI) (k := initX86) (fun _ hs => Proof.CmacTripleDes.X86.init_wp hs)
    (by lit_decide) nosp_init (by simp) hrsI h.fit h.pre (cov_frameI h.esp h.reads h.writes)
    (covW_frame h.writes) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, -⟩ := h.args
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  simp only [initX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, hK, m₂] at post
  have eK : Spec.TripleDes.bytesAt (pushed rsI s).mem (Kp.setWidth 64) KL =
      Spec.TripleDes.bytesAt s.mem (Kp.setWidth 64) KL := by
    simp only [Spec.TripleDes.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact (pushed_frame hrsI h.fit).bytes (R := ⟨Kp.setWidth 64, KL⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bK.symm)
      (by show KL ≤ 2 ^ 64; have := h.fK; omega) (List.mem_range.mp hi)
  rw [eK] at post
  exact post

theorem init_rel {Kp O S E : BitVec 32} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → IArgs s₁ Kp O S KL ∧ IArgs s₂ Kp O S KL ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P Impl.CmacTripleDes.Stream.X86.initFrame fun _ _ => True := by
  refine RelCT.frameInline (rs := rsI) (fun _ hs => Proof.CmacTripleDes.X86.init_wp hs)
    Proof.CmacTripleDes.X86.init_ct (iRd E Kp KL) (iWr O S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [e₁] at p₁
  rw [e₂] at p₂
  have c₁ := cov_frameI h₁.esp h₁.reads h₁.writes
  have c₂ := cov_frameI h₂.esp h₂.reads h₂.writes
  obtain ⟨a0, a1, a2, a3⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3⟩ := h₂.args
  refine ⟨e₁.trans e₂.symm, p₁, p₂, ⟨by simp only [State.withRegions_gpr, pushed_esp, e₁, e₂], fun i hi => ?_⟩,
    by subst e₁; exact c₁, covW_frame h₁.writes, by subst e₂; exact c₂, covW_frame h₂.writes⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]

end VG.Proof.CmacTripleDes.Stream.X86
