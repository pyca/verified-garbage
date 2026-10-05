import VerifiedGarbage.Proof.Aes.Arm.Ctr32
import VerifiedGarbage.Proof.Aes.Arm.ExpandKey
import VerifiedGarbage.Proof.Gcm.Arm.Ghash
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Impl.AesGcm.Arm
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.TCB.Arm.Isa

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Callee`. -/
section

/-!
# AES-GCM on ARMv7: the functions called

Untrusted: everything here is checked by Lean. Each call, from its callee's
contract (with `WP.call`), with the regions it is given: what it needs
(`CtrCall`, `GhCall`, `KeyCall`) and what it leaves (`CtrPost`, `GhPost`,
`KeyPost`); and that it is constant time (`ctr_rel`, `gh_rel`, `key_rel`).
`vg_aes_ctr32` and `vg_ghash` are called in a frame that pushes their stack
arguments (`push {r12, lr}`) in the 8 bytes below the stack pointer.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith)

/-! ## Memory -/

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := Proof.Cmac.bytesAt_frame hf hd hn

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, VG.Proof.AesGcm.Arm.bytesAt_frame hf hd (by decide)]

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    blocksAt m' p n = blocksAt m p n := by
  rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, VG.Proof.AesGcm.Arm.bytesAt_frame hf hd hn]

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 32 R).toNat = R :=
  VG.Proof.AesGcm.Arm.toNat_ofNat32 (by omega)

/-- Addresses below a pointer do not wrap. -/
theorem addr_sub {a : BitVec 32} {k : Nat} (h : k ≤ a.toNat) :
    State.addr (a - BitVec.ofNat 32 k) = State.addr a - BitVec.ofNat 64 k := by
  simp only [State.addr]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (a := a.toNat) (by omega)]
  omega

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- The 8 bytes below the stack pointer `sp`, where the frames push the stack
arguments. -/
abbrev below (sp : BitVec 32) : Region := ⟨State.addr sp - 8, 8⟩

theorem storeWords_two (m : Mem) (a : BitVec 32) (x y : BitVec 32) :
    storeWords m a [x, y] = (m.writeW (State.addr a) x).writeW (State.addr (a + 4)) y := rfl

theorem e8 : BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = 8 := rfl

section Push
variable {s : State} (hsp : 8 ≤ s.sp.toNat)
include hsp

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := VG.Proof.AesGcm.Arm.addr_sub hsp

theorem hspA : (s.sp - 8).toNat = s.sp.toNat - 8 :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hsp)

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  rw [addr_add (by rw [VG.Proof.AesGcm.Arm.hspA hsp]; omega), VG.Proof.AesGcm.Arm.hA hsp]; rfl

/-- The memory after `push {r12, lr}`. -/
theorem amem : (pushed [.r12, .lr] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) (s.gpr .r12)).writeW (State.addr s.sp - 8 + 4) (s.gpr .lr) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)) [s.gpr .r12, s.gpr .lr] = _
  rw [VG.Proof.AesGcm.Arm.e8, VG.Proof.AesGcm.Arm.storeWords_two, VG.Proof.AesGcm.Arm.hA hsp, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl,
    VG.Proof.AesGcm.Arm.hA4 hsp]

/-- The push writes only the 8 bytes below the stack pointer. -/
theorem fA : Frame [VG.Proof.AesGcm.Arm.below s.sp] s.mem (pushed [.r12, .lr] s).mem := by
  rw [VG.Proof.AesGcm.Arm.amem hsp]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; decide

omit hsp in
theorem pushed_sp8 : (pushed [.r12, .lr] s).sp = s.sp - 8 := by simp only [pushed_sp, VG.Proof.AesGcm.Arm.e8]

/-- The stack arguments the push leaves. -/
theorem arg0 : stackArg (pushed [.r12, .lr] s) 0 = s.gpr .r12 := by
  rw [stackArg, show stackArgAddr (pushed [.r12, .lr] s) 0 = State.addr s.sp - 8 by
      unfold stackArgAddr; rw [VG.Proof.AesGcm.Arm.pushed_sp8, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
        BitVec.add_zero _, VG.Proof.AesGcm.Arm.hA hsp],
    VG.Proof.AesGcm.Arm.amem hsp, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem arg1 : stackArg (pushed [.r12, .lr] s) 1 = s.gpr .lr := by
  rw [stackArg, show stackArgAddr (pushed [.r12, .lr] s) 1 = State.addr s.sp - 8 + 4 by
      unfold stackArgAddr; rw [VG.Proof.AesGcm.Arm.pushed_sp8]; exact VG.Proof.AesGcm.Arm.hA4 hsp,
    VG.Proof.AesGcm.Arm.amem hsp, Mem.readW_writeW_self32]

theorem argAddr0 : stackArgAddr (pushed [.r12, .lr] s) 0 = State.addr s.sp - 8 := by
  unfold stackArgAddr; rw [VG.Proof.AesGcm.Arm.pushed_sp8, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
    BitVec.add_zero _, VG.Proof.AesGcm.Arm.hA hsp]

/-- The register the pop loads is `r12`, as pushed, if the frame's body
changes nothing outside `rs`, which are apart from the 4 bytes below
the stack pointer's frame. -/
theorem popSlot {s₂ : State} {rs : List Region} (hf : Frame rs (pushed [.r12, .lr] s).mem s₂.mem)
    (hd : ∀ r ∈ rs, (⟨State.addr s.sp - 8, 4⟩ : Region).Disjoint r) :
    s₂.mem.readW (State.addr (pushed [.r12, .lr] s).sp) 32 = s.gpr .r12 := by
  rw [VG.Proof.AesGcm.Arm.pushed_sp8, VG.Proof.AesGcm.Arm.hA hsp, hf.readW (r := ⟨State.addr s.sp - 8, 4⟩) (a := State.addr s.sp - 8) (w := 32)
    (Region.contains_self _ _) hd (by decide), VG.Proof.AesGcm.Arm.amem hsp, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

end Push

@[simp] theorem stackArg_callEntry (s : State) (i : Nat) : stackArg s.callEntry i = stackArg s i := rfl
@[simp] theorem stackArgAddr_callEntry (s : State) (i : Nat) : stackArgAddr s.callEntry i = stackArgAddr s i := rfl

theorem view_gpr (s : State) (rd wr : List Region) (r : Reg) (hr : r ∉ linkRegs) :
    ((pushed [.r12, .lr] s).callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem view_sp (s : State) (rd wr : List Region) :
    ((pushed [.r12, .lr] s).callEntry.withRegions rd wr).sp = s.sp - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, VG.Proof.AesGcm.Arm.pushed_sp8]

theorem view_mem (s : State) (rd wr : List Region) :
    ((pushed [.r12, .lr] s).callEntry.withRegions rd wr).mem = (pushed [.r12, .lr] s).mem := by
  simp only [State.withRegions_mem, State.callEntry_mem]

theorem cover_pushed {s : State} {rs : List Region} (h : Covers rs s.wr) : Covers rs (pushed [.r12, .lr] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

theorem cover_pushed' {s : State} {rs : List Region} (h : Covers rs (s.rd ++ s.wr)) :
    Covers rs ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h x n' hi
  refine ⟨r', ?_, hc'⟩
  rcases List.mem_append.mp hr' with h' | h'
  · exact List.mem_append_left _ h'
  · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h')

theorem pushed_wr8 {s : State} (hsp : 8 ≤ s.sp.toNat) :
    (pushed [.r12, .lr] s).wr = ⟨State.addr s.sp - 8, 8⟩ :: s.wr := by
  rw [pushed_wr, show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, show BitVec.ofNat 32 8 = 8 from rfl, VG.Proof.AesGcm.Arm.hA hsp]

theorem cover_frame {s : State} (hsp : 8 ≤ s.sp.toNat) {n : Nat} (hn : n ≤ 8) :
    Covers [⟨State.addr s.sp - 8, n⟩] ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  intro x n' ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨_, List.mem_append_right _ (by rw [VG.Proof.AesGcm.Arm.pushed_wr8 hsp]; exact List.mem_cons_self ..), ?_⟩
  simp only [Region.Contains] at hc ⊢; omega

theorem covers_append' {xs ys ts : List Region} (h₁ : Covers xs ts) (h₂ : Covers ys ts) :
    Covers (xs ++ ys) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ a n ⟨x, hx, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem ctr_noCalls : Impl.Aes.Arm.ctr32.noCalls = true := by decide +kernel
theorem gh_noCalls : Impl.Gcm.Arm.ghash.noCalls = true := by decide +kernel
theorem key_noCalls : Impl.Aes.Arm.expandKey.noCalls = true := by decide +kernel

/-! ## `vg_aes_ctr32` -/

/-- What a call of `vg_aes_ctr32` needs: the key schedule at `K` for `R`
rounds, the counter block at `C`, `n` blocks at `D` and working space at `S`,
with `n` in `r12` and `S` in `lr`, to push. -/
structure CtrCall (s : State) (K C D S : BitVec 32) (R n : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  r12 : s.gpr .r12 = BitVec.ofNat 32 n
  lr : s.gpr .lr = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  hsp : 8 ≤ s.sp.toNat
  fitK : K.toNat + 240 ≤ 2 ^ 32
  fitC : C.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  fitS : S.toNat + 2048 ≤ 2 ^ 32
  kc : (⟨State.addr K, 240⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  kd : (⟨State.addr K, 240⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  ks : (⟨State.addr K, 240⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  cd : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  cs : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2048⟩
  bk : (VG.Proof.AesGcm.Arm.below s.sp).Disjoint ⟨State.addr K, 240⟩
  bc : (VG.Proof.AesGcm.Arm.below s.sp).Disjoint ⟨State.addr C, 16⟩
  bd : (VG.Proof.AesGcm.Arm.below s.sp).Disjoint ⟨State.addr D, 16 * n⟩
  bs : (VG.Proof.AesGcm.Arm.below s.sp).Disjoint ⟨State.addr S, 2048⟩
  reads : Covers [⟨State.addr K, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2048⟩] s.wr

/-- What a call of `vg_aes_ctr32` leaves. -/
structure CtrPost (s : State) (K C D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2048⟩, VG.Proof.AesGcm.Arm.below s.sp] s.mem s'.mem
  out : blocksAt s'.mem (State.addr D) n =
    ctr32 (aesWith R (bytesAt s.mem (State.addr K) (16 * (R + 1)))) (blockAt s.mem (State.addr C))
      (blocksAt s.mem (State.addr D) n)
  ctr : blockAt s'.mem (State.addr C) = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem (State.addr C))

abbrev ctrRd (sp K : BitVec 32) : List Region := [⟨State.addr K, 240⟩, VG.Proof.AesGcm.Arm.below sp]
abbrev ctrWr (C D S : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2048⟩]

namespace CtrCall
variable {s : State} {K C D S : BitVec 32} {R n : Nat} (h : VG.Proof.AesGcm.Arm.CtrCall s K C D S R n)
include h

theorem n_lt : n < 2 ^ 32 := by have := h.fitD; omega

theorem pre : Proof.Aes.ctr32Arm.pre
    ((pushed [.r12, .lr] s).callEntry.withRegions (VG.Proof.AesGcm.Arm.ctrRd s.sp K) (VG.Proof.AesGcm.Arm.ctrWr C D S n)) := by
  have hR := VG.Proof.AesGcm.Arm.toNat_rounds h.rounds
  have hn := VG.Proof.AesGcm.Arm.toNat_ofNat32 h.n_lt
  simp only [Proof.Aes.ctr32Arm, VG.Proof.AesGcm.Arm.arg0 h.hsp, VG.Proof.AesGcm.Arm.arg1 h.hsp, VG.Proof.AesGcm.Arm.argAddr0 h.hsp, VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r0 (by decide),
    VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r1 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r2 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, h.r12, h.lr, hR, hn, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, VG.Proof.AesGcm.Arm.view_sp, VG.Proof.AesGcm.Arm.hspA h.hsp, stackArgAddr_withRegions, stackArg_withRegions, VG.Proof.AesGcm.Arm.stackArg_callEntry,
    VG.Proof.AesGcm.Arm.stackArgAddr_callEntry, VG.Proof.AesGcm.Arm.arg0 h.hsp, VG.Proof.AesGcm.Arm.arg1 h.hsp, VG.Proof.AesGcm.Arm.argAddr0 h.hsp, h.r12, h.lr, hn]
  refine ⟨trivial, trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.bc.symm, h.bd.symm, h.bs.symm, h.fitK,
    h.fitC, h.fitD, h.fitS, ?_, h.rounds⟩
  have := s.sp.isLt; omega

theorem cov : Covers (VG.Proof.AesGcm.Arm.ctrRd s.sp K ++ VG.Proof.AesGcm.Arm.ctrWr C D S n)
    ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  refine VG.Proof.AesGcm.Arm.covers_append' (VG.Proof.AesGcm.Arm.covers_append' (VG.Proof.AesGcm.Arm.cover_pushed' h.reads) (VG.Proof.AesGcm.Arm.cover_frame h.hsp (by decide)))
    (VG.Proof.AesGcm.Arm.cover_pushed' (fun x n' hi => ?_))
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem covW : Covers (VG.Proof.AesGcm.Arm.ctrWr C D S n) (pushed [.r12, .lr] s).wr := VG.Proof.AesGcm.Arm.cover_pushed h.writes

end CtrCall

theorem ctr_call {s : State} {K C D S : BitVec 32} {R n : Nat} (h : VG.Proof.AesGcm.Arm.CtrCall s K C D S R n) :
    WP isa ctrFrame s (VG.Proof.AesGcm.Arm.CtrPost s K C D S R n) := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := Proof.Aes.ctr32Arm) Proof.Aes.Arm.ctr32_correct
    (rd := VG.Proof.AesGcm.Arm.ctrRd s.sp K) (wr := VG.Proof.AesGcm.Arm.ctrWr C D S n) h.pre h.cov h.covW ?_ VG.Proof.AesGcm.Arm.ctr_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have hR := VG.Proof.AesGcm.Arm.toNat_rounds h.rounds
  have hn := VG.Proof.AesGcm.Arm.toNat_ofNat32 h.n_lt
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  have fA' := VG.Proof.AesGcm.Arm.fA (s := s) h.hsp
  have bytesK : bytesAt (pushed [.r12, .lr] s).mem (State.addr K) (16 * (R + 1)) =
      bytesAt s.mem (State.addr K) (16 * (R + 1)) :=
    VG.Proof.AesGcm.Arm.bytesAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bk.symm.sub_left (Region.sub_prefix hR'))) (by omega)
  have blockC : blockAt (pushed [.r12, .lr] s).mem (State.addr C) = blockAt s.mem (State.addr C) :=
    VG.Proof.AesGcm.Arm.blockAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bc.symm)
  have blocksD : blocksAt (pushed [.r12, .lr] s).mem (State.addr D) n = blocksAt s.mem (State.addr D) n :=
    VG.Proof.AesGcm.Arm.blocksAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm) (by have := h.fitD; omega)
  obtain ⟨hdata, hctr⟩ := hpost
  simp only [State.withRegions_mem, State.callEntry_mem, VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r0 (by decide),
    VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r1 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r2 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, hR, stackArg_withRegions, VG.Proof.AesGcm.Arm.stackArg_callEntry, VG.Proof.AesGcm.Arm.arg0 h.hsp, h.r12, hn, bytesK, blockC, blocksD] at hdata hctr
  have fB : Frame (VG.Proof.AesGcm.Arm.ctrWr C D S n) (pushed [.r12, .lr] s).mem s₂.mem := hf
  have slot : s₂.mem.readW (State.addr (pushed [.r12, .lr] s).sp) 32 = s.gpr .r12 :=
    VG.Proof.AesGcm.Arm.popSlot h.hsp fB (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (h.bc.sub_left (Region.sub_prefix (by decide)))
      · exact (h.bd.sub_left (Region.sub_prefix (by decide)))
      · exact (h.bs.sub_left (Region.sub_prefix (by decide))))
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, VG.Proof.AesGcm.Arm.pushed_sp8]; exact BitVec.sub_add_cancel _ _
  · by_cases h12 : r = .r12
    · subst h12
      show (s₂.setReg .r12 (s₂.mem.readW (State.addr s₂.sp) 32)).gpr .r12 = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, hsp₂, slot]
    · rw [popped_gpr h12, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine (fA'.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (fB.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact hdata
  · rw [popped_mem]; exact hctr

/-- Calls of `vg_aes_ctr32` with the same arguments and stack pointer in both
runs are constant time. -/
theorem ctr_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D S : BitVec 32, ∃ R n : Nat,
      VG.Proof.AesGcm.Arm.CtrCall s₁ K C D S R n ∧ VG.Proof.AesGcm.Arm.CtrCall s₂ K C D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P ctrFrame fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, _, _, _, _, _, _, e⟩ := h _ _ hp; exact e) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, hp, pa, pb⟩ e₁ e₂
  obtain ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩ := h _ _ hp
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  refine RelCT.call (k := Proof.Aes.ctr32Arm) Proof.Aes.Arm.ctr32_correct Proof.Aes.Arm.ctr32_ct
    (VG.Proof.AesGcm.Arm.ctrRd s₁.sp K) (VG.Proof.AesGcm.Arm.ctrWr C D S n) (P := fun x y => x = pushed [.r12, .lr] s₁ ∧ y = pushed [.r12, .lr] s₂)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [← hsp] at p₂
  refine ⟨p₁, p₂, ?_, h₁.cov, h₁.covW, hsp ▸ h₂.cov, h₂.covW⟩
  simp only [Proof.Aes.ctr32Arm, stackArg_withRegions, VG.Proof.AesGcm.Arm.stackArg_callEntry, VG.Proof.AesGcm.Arm.arg0 h₁.hsp, VG.Proof.AesGcm.Arm.arg1 h₁.hsp, VG.Proof.AesGcm.Arm.arg0 h₂.hsp, VG.Proof.AesGcm.Arm.arg1 h₂.hsp,
    VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r0 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r1 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r2 (by decide),
    VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r3 (by decide), VG.Proof.AesGcm.Arm.view_sp, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₁.lr, h₂.r0, h₂.r1, h₂.r2,
    h₂.r3, h₂.r12, h₂.lr, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_ghash` -/

/-- What a call of `vg_ghash` needs: the hash subkey at `H`, the accumulator
at `Y`, `n` blocks at `D` and working space at `S`, in `r12` to push. -/
structure GhCall (s : State) (H Y D S : BitVec 32) (n : Nat) : Prop where
  r0 : s.gpr .r0 = H
  r1 : s.gpr .r1 = Y
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = BitVec.ofNat 32 n
  r12 : s.gpr .r12 = S
  hsp : 8 ≤ s.sp.toNat
  fitH : H.toNat + 16 ≤ 2 ^ 32
  fitY : Y.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  fitS : S.toNat + 256 ≤ 2 ^ 32
  hy : (⟨State.addr H, 16⟩ : Region).Disjoint ⟨State.addr Y, 16⟩
  hs : (⟨State.addr H, 16⟩ : Region).Disjoint ⟨State.addr S, 256⟩
  yd : (⟨State.addr Y, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  ys : (⟨State.addr Y, 16⟩ : Region).Disjoint ⟨State.addr S, 256⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 256⟩
  bh : (VG.Proof.AesGcm.Arm.below s.sp).Disjoint ⟨State.addr H, 16⟩
  by' : (VG.Proof.AesGcm.Arm.below s.sp).Disjoint ⟨State.addr Y, 16⟩
  bd : (VG.Proof.AesGcm.Arm.below s.sp).Disjoint ⟨State.addr D, 16 * n⟩
  bs : (VG.Proof.AesGcm.Arm.below s.sp).Disjoint ⟨State.addr S, 256⟩
  reads : Covers [⟨State.addr H, 16⟩, ⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr Y, 16⟩, ⟨State.addr S, 256⟩] s.wr

/-- What a call of `vg_ghash` leaves. -/
structure GhPost (s : State) (H Y D S : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr Y, 16⟩, ⟨State.addr S, 256⟩, VG.Proof.AesGcm.Arm.below s.sp] s.mem s'.mem
  out : blockAt s'.mem (State.addr Y) =
    ghashFrom (blockAt s.mem (State.addr H)) (blockAt s.mem (State.addr Y)) (blocksAt s.mem (State.addr D) n)

abbrev ghRd (sp H D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr H, 16⟩, ⟨State.addr D, 16 * n⟩, ⟨State.addr sp - 8, 4⟩]
abbrev ghWr (Y S : BitVec 32) : List Region := [⟨State.addr Y, 16⟩, ⟨State.addr S, 256⟩]

namespace GhCall
variable {s : State} {H Y D S : BitVec 32} {n : Nat} (h : VG.Proof.AesGcm.Arm.GhCall s H Y D S n)
include h

theorem n_lt : n < 2 ^ 32 := by have := h.fitD; omega

theorem pre : Proof.Gcm.ghashArm.pre
    ((pushed [.r12, .lr] s).callEntry.withRegions (VG.Proof.AesGcm.Arm.ghRd s.sp H D n) (VG.Proof.AesGcm.Arm.ghWr Y S)) := by
  have hn := VG.Proof.AesGcm.Arm.toNat_ofNat32 h.n_lt
  have b4 : ∀ x : Region, (VG.Proof.AesGcm.Arm.below s.sp).Disjoint x → (⟨State.addr s.sp - 8, 4⟩ : Region).Disjoint x :=
    fun x hx => hx.sub_left (Region.sub_prefix (by decide))
  simp only [Proof.Gcm.ghashArm, VG.Proof.AesGcm.Arm.arg0 h.hsp, VG.Proof.AesGcm.Arm.argAddr0 h.hsp, VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r0 (by decide),
    VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r1 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r2 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, h.r12, hn, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, VG.Proof.AesGcm.Arm.view_sp, VG.Proof.AesGcm.Arm.hspA h.hsp, stackArgAddr_withRegions, stackArg_withRegions, VG.Proof.AesGcm.Arm.stackArg_callEntry,
    VG.Proof.AesGcm.Arm.stackArgAddr_callEntry, VG.Proof.AesGcm.Arm.arg0 h.hsp, VG.Proof.AesGcm.Arm.arg1 h.hsp, VG.Proof.AesGcm.Arm.argAddr0 h.hsp, h.r12, hn]
  refine ⟨trivial, trivial, h.hy, h.hs, h.yd, h.ys, h.ds, (b4 _ h.by').symm, (b4 _ h.bs).symm, h.fitH, h.fitY,
    h.fitD, h.fitS, ?_⟩
  have := s.sp.isLt; omega

theorem cov : Covers (VG.Proof.AesGcm.Arm.ghRd s.sp H D n ++ VG.Proof.AesGcm.Arm.ghWr Y S)
    ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  have e : VG.Proof.AesGcm.Arm.ghRd s.sp H D n = [⟨State.addr H, 16⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr s.sp - 8, 4⟩] := rfl
  rw [e]
  refine VG.Proof.AesGcm.Arm.covers_append' (VG.Proof.AesGcm.Arm.covers_append' (VG.Proof.AesGcm.Arm.cover_pushed' h.reads) (VG.Proof.AesGcm.Arm.cover_frame h.hsp (by decide)))
    (VG.Proof.AesGcm.Arm.cover_pushed' (fun x n' hi => ?_))
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem covW : Covers (VG.Proof.AesGcm.Arm.ghWr Y S) (pushed [.r12, .lr] s).wr := VG.Proof.AesGcm.Arm.cover_pushed h.writes

end GhCall

theorem gh_call {s : State} {H Y D S : BitVec 32} {n : Nat} (h : VG.Proof.AesGcm.Arm.GhCall s H Y D S n) :
    WP isa ghFrame s (VG.Proof.AesGcm.Arm.GhPost s H Y D S n) := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := Proof.Gcm.ghashArm) Proof.Gcm.Arm.ghash_correct
    (rd := VG.Proof.AesGcm.Arm.ghRd s.sp H D n) (wr := VG.Proof.AesGcm.Arm.ghWr Y S) h.pre h.cov h.covW ?_ VG.Proof.AesGcm.Arm.gh_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have hn := VG.Proof.AesGcm.Arm.toNat_ofNat32 h.n_lt
  have fA' := VG.Proof.AesGcm.Arm.fA (s := s) h.hsp
  have blockH : blockAt (pushed [.r12, .lr] s).mem (State.addr H) = blockAt s.mem (State.addr H) :=
    VG.Proof.AesGcm.Arm.blockAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bh.symm)
  have blockY : blockAt (pushed [.r12, .lr] s).mem (State.addr Y) = blockAt s.mem (State.addr Y) :=
    VG.Proof.AesGcm.Arm.blockAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.by'.symm)
  have blocksD : blocksAt (pushed [.r12, .lr] s).mem (State.addr D) n = blocksAt s.mem (State.addr D) n :=
    VG.Proof.AesGcm.Arm.blocksAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bd.symm) (by have := h.fitD; omega)
  simp only [Proof.Gcm.ghashArm, State.withRegions_mem, State.callEntry_mem, VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r0 (by decide),
    VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r1 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r2 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, hn, blockH, blockY, blocksD] at hpost
  have fB : Frame (VG.Proof.AesGcm.Arm.ghWr Y S) (pushed [.r12, .lr] s).mem s₂.mem := hf
  have slot : s₂.mem.readW (State.addr (pushed [.r12, .lr] s).sp) 32 = s.gpr .r12 :=
    VG.Proof.AesGcm.Arm.popSlot h.hsp fB (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.by'.sub_left (Region.sub_prefix (by decide)))
      · exact (h.bs.sub_left (Region.sub_prefix (by decide))))
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, VG.Proof.AesGcm.Arm.pushed_sp8]; exact BitVec.sub_add_cancel _ _
  · by_cases h12 : r = .r12
    · subst h12
      show (s₂.setReg .r12 (s₂.mem.readW (State.addr s₂.sp) 32)).gpr .r12 = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, hsp₂, slot]
    · rw [popped_gpr h12, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine (fA'.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (fB.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact hpost

theorem gh_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ H Y D S : BitVec 32, ∃ n : Nat,
      VG.Proof.AesGcm.Arm.GhCall s₁ H Y D S n ∧ VG.Proof.AesGcm.Arm.GhCall s₂ H Y D S n ∧ s₁.sp = s₂.sp) :
    RelCT isa P ghFrame fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, _, _, _, _, _, e⟩ := h _ _ hp; exact e) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, hp, pa, pb⟩ e₁ e₂
  obtain ⟨H, Y, D, S, n, h₁, h₂, hsp⟩ := h _ _ hp
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  refine RelCT.call (k := Proof.Gcm.ghashArm) Proof.Gcm.Arm.ghash_correct Proof.Gcm.Arm.ghash_ct
    (VG.Proof.AesGcm.Arm.ghRd s₁.sp H D n) (VG.Proof.AesGcm.Arm.ghWr Y S) (P := fun x y => x = pushed [.r12, .lr] s₁ ∧ y = pushed [.r12, .lr] s₂)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [← hsp] at p₂
  refine ⟨p₁, p₂, ?_, h₁.cov, h₁.covW, hsp ▸ h₂.cov, h₂.covW⟩
  simp only [Proof.Gcm.ghashArm, stackArg_withRegions, VG.Proof.AesGcm.Arm.stackArg_callEntry, VG.Proof.AesGcm.Arm.arg0 h₁.hsp, VG.Proof.AesGcm.Arm.arg0 h₂.hsp,
    VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r0 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r1 (by decide), VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r2 (by decide),
    VG.Proof.AesGcm.Arm.view_gpr _ _ _ .r3 (by decide), VG.Proof.AesGcm.Arm.view_sp, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₂.r0, h₂.r1, h₂.r2,
    h₂.r3, h₂.r12, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key_scratch` -/

/-- What a call of `vg_aes_expand_key_scratch` needs: the `L`-byte key at `K`, the key
schedule at `C` and working space at `S`. -/
structure KeyCall (s : State) (K C S : BitVec 32) (L : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = BitVec.ofNat 32 L
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = S
  len : L = 16 ∨ L = 24 ∨ L = 32
  fitK : K.toNat + L ≤ 2 ^ 32
  fitC : C.toNat + 240 ≤ 2 ^ 32
  fitS : S.toNat + 512 ≤ 2 ^ 32
  kc : (⟨State.addr K, L⟩ : Region).Disjoint ⟨State.addr C, 240⟩
  ks : (⟨State.addr K, L⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  cs : (⟨State.addr C, 240⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  reads : Covers [⟨State.addr K, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 240⟩, ⟨State.addr S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key_scratch` leaves. -/
structure KeyPost (s : State) (K C S : BitVec 32) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 240⟩, ⟨State.addr S, 512⟩] s.mem s'.mem
  out : bytesAt s'.mem (State.addr C) (16 * (Spec.Aes.rounds (L / 4) + 1)) =
    Spec.Aes.expandKey (bytesAt s.mem (State.addr K) L)

namespace KeyCall
variable {s : State} {K C S : BitVec 32} {L : Nat} (h : VG.Proof.AesGcm.Arm.KeyCall s K C S L)
include h

theorem hL : (BitVec.ofNat 32 L).toNat = L :=
  VG.Proof.AesGcm.Arm.toNat_ofNat32 (by rcases h.len with h' | h' | h' <;> omega)

theorem pre : Proof.Aes.expandKeyArm.pre
    (s.callEntry.withRegions [⟨State.addr K, L⟩] [⟨State.addr C, 240⟩, ⟨State.addr S, 512⟩]) := by
  simp only [Proof.Aes.expandKeyArm, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
    h.r0, h.r1, h.r2, h.r3, h.hL]
  exact ⟨trivial, trivial, h.kc, h.ks, h.cs, h.fitK, h.fitC, h.fitS, h.len⟩

end KeyCall

theorem key_call {s : State} {K C S : BitVec 32} {L : Nat} (h : KeyCall s K C S L) :
    WP isa (.call "vg_aes_expand_key_scratch" Impl.Aes.Arm.expandKey) s (KeyPost s K C S L) := by
  refine WP.call (k := Proof.Aes.expandKeyArm) Proof.Aes.Arm.expandKey_correct
    (rd := [⟨State.addr K, L⟩]) (wr := [⟨State.addr C, 240⟩, ⟨State.addr S, 512⟩]) h.pre
    (VG.Proof.AesGcm.Arm.covers_append' h.reads (fun x n' hi => by
      obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
      exact ⟨r', List.mem_append_right _ hr', hc'⟩)) h.writes ?_ VG.Proof.AesGcm.Arm.key_noCalls
  intro s' hrd hwr hsp hf hcs _ hpost
  simp only [Proof.Aes.expandKeyArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr s (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.r2 ∉ linkRegs), h.r0, h.r1, h.r2, h.hL] at hpost
  exact ⟨hrd, hwr, hsp, hcs, hf, hpost⟩

theorem key_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C S : BitVec 32, ∃ L : Nat, KeyCall s₁ K C S L ∧ KeyCall s₂ K C S L) :
    RelCT isa P (.call "vg_aes_expand_key_scratch" Impl.Aes.Arm.expandKey) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨K, C, S, L, h₁, h₂⟩ := h _ _ hp
  have cov : ∀ {s : State}, VG.Proof.AesGcm.Arm.KeyCall s K C S L →
      Covers ([⟨State.addr K, L⟩] ++ [⟨State.addr C, 240⟩, ⟨State.addr S, 512⟩]) (s.rd ++ s.wr) :=
    fun {s} hk => VG.Proof.AesGcm.Arm.covers_append' hk.reads (fun x n' hi => by
      obtain ⟨r', hr', hc'⟩ := hk.writes x n' hi
      exact ⟨r', List.mem_append_right _ hr', hc'⟩)
  refine RelCT.call (k := Proof.Aes.expandKeyArm) Proof.Aes.Arm.expandKey_correct Proof.Aes.Arm.expandKey_ct
    [⟨State.addr K, L⟩] [⟨State.addr C, 240⟩, ⟨State.addr S, 512⟩] (P := fun x y => x = s₁ ∧ y = s₂)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  refine ⟨h₁.pre, h₂.pre, ?_, cov h₁, h₁.writes, cov h₂, h₂.writes⟩
  simp only [Proof.Aes.expandKeyArm, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1, h₂.r2, h₂.r3]
  exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Env`. -/
section

/-!
# AES-GCM on ARMv7: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes at
`c`), the streaming state (80 bytes at `st`), the working space (2560 bytes at
`w`) and the 8 bytes below the stack pointer `sp` used by the frames (`Lay`),
all 32-bit pointers: the state is disjoint from the parts of `W` other than
`[16, 96)` (where `seal` and `open` keep it), and the context from both.
`Perm` says the state may read the context and write the state and `W`;
`Env` adds the registers that hold the three pointers throughout, and the
stack pointer.

Memory is addressed with 64-bit addresses at offsets of `State.addr p`; the
code's 32-bit sums do not wrap (`Lay.cA`, `Lay.stA`, `Lay.wA`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)

/-- The part of a region at an offset is covered when the region is. -/
theorem covers_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine h a m ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.Arm.covers_off h hd hk _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem in_left {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_left {rd wr rs : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) :=
  fun a n hi => VG.Proof.AesGcm.Arm.in_left (h a n hi)

theorem covers_cons {r : Region} {rs ts : List Region} (h₁ : Covers [r] ts) (h₂ : Covers rs ts) :
    Covers (r :: rs) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁ a n ⟨x, List.mem_singleton_self _, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem covers_nil {ts : List Region} : Covers [] ts := fun _ _ ⟨_, h, _⟩ => by cases h

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

theorem add_ofNat_zero {w : Nat} (x : BitVec w) : x + BitVec.ofNat w 0 = x := BitVec.add_zero x

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem add32_ofNat_assoc (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The regions: the context, the state and the parts of `W`, and the stack
below `sp` (8 bytes, for the frames of the calls). -/
structure Lay (c st w sp : BitVec 32) : Prop where
  cw : c.toNat + 256 ≤ 2 ^ 32
  sw : st.toNat + 80 ≤ 2 ^ 32
  ww : w.toNat + 2560 ≤ 2 ^ 32
  sp8 : 8 ≤ sp.toNat
  cs : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr st, 80⟩
  cw' : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  sa : (⟨State.addr st, 80⟩ : Region).Disjoint ⟨State.addr w, 16⟩
  sb : (⟨State.addr st, 80⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 96, 2464⟩
  kc : (VG.Proof.AesGcm.Arm.below sp).Disjoint ⟨State.addr c, 256⟩
  ks : (VG.Proof.AesGcm.Arm.below sp).Disjoint ⟨State.addr st, 80⟩
  kw : (VG.Proof.AesGcm.Arm.below sp).Disjoint ⟨State.addr w, 2560⟩

/-- What a state may access. -/
structure Perm (c st w : BitVec 32) (s : State) : Prop where
  ctx : Covers [⟨State.addr c, 256⟩] (s.rd ++ s.wr)
  st : Covers [⟨State.addr st, 80⟩] s.wr
  w : Covers [⟨State.addr w, 2560⟩] s.wr

/-- The registers holding the context, the state and `W`, the stack pointer,
what the state may access, and the values `k7`, `k8` of `r7` and `r8`, which
the pieces keep (the number of rounds, or a length). -/
structure Env (c st w sp k7 k8 : BitVec 32) (s : State) : Prop where
  r7 : s.gpr .r7 = k7
  r8 : s.gpr .r8 = k8
  r9 : s.gpr .r9 = c
  r10 : s.gpr .r10 = st
  r11 : s.gpr .r11 = w
  sp : s.sp = sp
  perm : VG.Proof.AesGcm.Arm.Perm c st w s

theorem Perm.of_eq {c st w : BitVec 32} {s s' : State} (h : VG.Proof.AesGcm.Arm.Perm c st w s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.Arm.Perm c st w s' := by
  obtain ⟨a, b, d⟩ := h; exact ⟨by rw [hrd, hwr]; exact a, by rw [hwr]; exact b, by rw [hwr]; exact d⟩

/-- An environment, after code that keeps `r7`–`r11`, `sp` and the permissions. -/
theorem Env.keep {c st w sp k7 k8 : BitVec 32} {s s' : State} (h : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s)
    (hg : ∀ r ∈ [Reg.r7, .r8, .r9, .r10, .r11], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s' :=
  ⟨by rw [hg _ (by simp), h.r7], by rw [hg _ (by simp), h.r8], by rw [hg _ (by simp), h.r9],
    by rw [hg _ (by simp), h.r10], by rw [hg _ (by simp), h.r11], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after a call. -/
theorem Env.of_saved {c st w sp k7 k8 : BitVec 32} {s s' : State} (h : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

/-- An environment with a new value of `r7`. -/
theorem Env.set7 {c st w sp k7 k8 k7' : BitVec 32} {s s' : State} (h : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s)
    (h7 : s'.gpr .r7 = k7') (hg : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.Arm.Env c st w sp k7' k8 s' :=
  ⟨h7, by rw [hg _ (by simp), h.r8], by rw [hg _ (by simp), h.r9],
    by rw [hg _ (by simp), h.r10], by rw [hg _ (by simp), h.r11], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

namespace Lay

/-! ### Sub-regions -/

theorem ctxSub {C : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ ⟨C, 256⟩ :=
  Offset.sub_base _ h

theorem stSub {S : Addr} {d n : Nat} (h : d + n ≤ 80) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 80⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

theorem bSub {W : Addr} {d n : Nat} (h₁ : 96 ≤ d) (h₂ : d + n ≤ 2560) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W + BitVec.ofNat 64 96, 2464⟩ :=
  Offset.sub _ h₁ (by omega)

theorem aSub {W : Addr} {d n : Nat} (h : d + n ≤ 16) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 16⟩ :=
  Offset.sub_base _ h

variable {c st w sp : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp)
include L

/-! ### The code's sums do not wrap -/

theorem cA {d : Nat} (hd : d < 256) : State.addr (c + BitVec.ofNat 32 d) = State.addr c + BitVec.ofNat 64 d :=
  addr_add (by have := L.cw; omega)

theorem stA {d : Nat} (hd : d < 80) : State.addr (st + BitVec.ofNat 32 d) = State.addr st + BitVec.ofNat 64 d :=
  addr_add (by have := L.sw; omega)

theorem wA {d : Nat} (hd : d < 2560) : State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
  addr_add (by have := L.ww; omega)

/-- Parts of the state and of `W` outside `[16, 96)` are disjoint. -/
theorem st_w {a n d k : Nat} (ha : a + n ≤ 80) (hd : (d + k ≤ 16) ∨ (96 ≤ d ∧ d + k ≤ 2560)) :
    (⟨State.addr st + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, k⟩ := by
  rcases hd with hd | ⟨h₁, h₂⟩
  · exact (L.sa.sub_left (VG.Proof.AesGcm.Arm.Lay.stSub ha)).sub_right (VG.Proof.AesGcm.Arm.Lay.aSub hd)
  · exact (L.sb.sub_left (VG.Proof.AesGcm.Arm.Lay.stSub ha)).sub_right (VG.Proof.AesGcm.Arm.Lay.bSub h₁ h₂)

theorem ctx_st {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 80) :
    (⟨State.addr c + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr st + BitVec.ofNat 64 d, k⟩ :=
  (L.cs.sub_left (VG.Proof.AesGcm.Arm.Lay.ctxSub ha)).sub_right (VG.Proof.AesGcm.Arm.Lay.stSub hd)

theorem ctx_w {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 2560) :
    (⟨State.addr c + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, k⟩ :=
  (L.cw'.sub_left (VG.Proof.AesGcm.Arm.Lay.ctxSub ha)).sub_right (VG.Proof.AesGcm.Arm.Lay.wSub hd)

theorem stk_ctx {a n : Nat} (ha : a + n ≤ 256) :
    (VG.Proof.AesGcm.Arm.below sp).Disjoint ⟨State.addr c + BitVec.ofNat 64 a, n⟩ := L.kc.sub_right (VG.Proof.AesGcm.Arm.Lay.ctxSub ha)

theorem stk_st {a n : Nat} (ha : a + n ≤ 80) :
    (VG.Proof.AesGcm.Arm.below sp).Disjoint ⟨State.addr st + BitVec.ofNat 64 a, n⟩ := L.ks.sub_right (VG.Proof.AesGcm.Arm.Lay.stSub ha)

theorem stk_w {a n : Nat} (ha : a + n ≤ 2560) :
    (VG.Proof.AesGcm.Arm.below sp).Disjoint ⟨State.addr w + BitVec.ofNat 64 a, n⟩ := L.kw.sub_right (VG.Proof.AesGcm.Arm.Lay.wSub ha)

omit L in
/-- Parts of the state are disjoint. -/
theorem st_st {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 80) (hd : d + k ≤ 80) :
    (⟨State.addr st + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr st + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

omit L in
/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨State.addr w + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

omit L in
theorem ctx_ctx {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 256) (hd : d + k ≤ 256) :
    (⟨State.addr c + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr c + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

/-- The 32-bit sums of the pointers, as numbers. -/
theorem cN {d : Nat} (hd : d < 256) : (c + BitVec.ofNat 32 d).toNat = c.toNat + d := by
  have := L.cw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem stN {d : Nat} (hd : d < 80) : (st + BitVec.ofNat 32 d).toNat = st.toNat + d := by
  have := L.sw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem wN {d : Nat} (hd : d < 2560) : (w + BitVec.ofNat 32 d).toNat = w.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

end Lay

namespace Perm

variable {c st w : BitVec 32} {s : State} (P : VG.Proof.AesGcm.Arm.Perm c st w s)
include P

theorem ctxR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (State.addr c + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.Arm.in_off P.ctx h (by decide)

theorem stW {d n : Nat} (h : d + n ≤ 80) : InRegions s.wr (State.addr st + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.Arm.in_off P.st h (by decide)

theorem stR {d n : Nat} (h : d + n ≤ 80) : InRegions (s.rd ++ s.wr) (State.addr st + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.Arm.in_left (P.stW h)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (State.addr w + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.Arm.in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (State.addr w + BitVec.ofNat 64 d) n :=
  VG.Proof.AesGcm.Arm.in_left (P.wW h)

theorem ctxC {d n : Nat} (h : d + n ≤ 256) : Covers [⟨State.addr c + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  VG.Proof.AesGcm.Arm.covers_off P.ctx h (by decide)

theorem stC {d n : Nat} (h : d + n ≤ 80) : Covers [⟨State.addr st + BitVec.ofNat 64 d, n⟩] s.wr :=
  VG.Proof.AesGcm.Arm.covers_off P.st h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨State.addr w + BitVec.ofNat 64 d, n⟩] s.wr :=
  VG.Proof.AesGcm.Arm.covers_off P.w h (by decide)

end Perm

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Run`. -/
section

/-!
# AES-GCM on ARMv7: running straight-line blocks

Untrusted: everything here is checked by Lean. `arun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`), and
the memory facts shared by the pieces: what `DataOk` says of a buffer of
data, and the bytes written by a copy (`bytesAt_writeBytes`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)

@[simp] theorem gpr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).gpr = s.gpr := rfl
@[simp] theorem mem_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl
@[simp] theorem rd_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl
@[simp] theorem wr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
@[simp] theorem sp_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).sp = s.sp := rfl
@[simp] theorem z_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).z = (x - y == 0) := rfl
@[simp] theorem c_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).c = decide (y.toNat ≤ x.toNat) := rfl
/-- `s` with the memory `m`: what a store leaves, kept folded in symbolic
execution (unfolded, the structure update would copy the state into each
of its fields). -/
def withMem (s : State) (m : Mem) : State := { s with mem := m }

theorem store32_eq (s : State) (a : Addr) (x : BitVec 32) :
    s.store32 a x = if InRegions s.wr a 4 then some (VG.Proof.AesGcm.Arm.withMem s (s.mem.writeW a x)) else none := rfl
theorem store8_eq (s : State) (a : Addr) (x : BitVec 8) :
    s.store8 a x = if InRegions s.wr a 1 then some (VG.Proof.AesGcm.Arm.withMem s (s.mem.writeW a x)) else none := rfl
@[simp] theorem sp_store (s : State) (m : Mem) : (VG.Proof.AesGcm.Arm.withMem s m).sp = s.sp := rfl
@[simp] theorem gpr_store (s : State) (m : Mem) : (VG.Proof.AesGcm.Arm.withMem s m).gpr = s.gpr := rfl
@[simp] theorem rd_store (s : State) (m : Mem) : (VG.Proof.AesGcm.Arm.withMem s m).rd = s.rd := rfl
@[simp] theorem wr_store (s : State) (m : Mem) : (VG.Proof.AesGcm.Arm.withMem s m).wr = s.wr := rfl
@[simp] theorem mem_store (s : State) (m : Mem) : (VG.Proof.AesGcm.Arm.withMem s m).mem = m := rfl
@[simp] theorem z_store (s : State) (m : Mem) : (VG.Proof.AesGcm.Arm.withMem s m).z = s.z := rfl
@[simp] theorem c_store (s : State) (m : Mem) : (VG.Proof.AesGcm.Arm.withMem s m).c = s.c := rfl

theorem op2_imm' {s : State} {n : Nat} (h : encodable (BitVec.ofNat 32 n) = true) :
    (imm n).eval s = some (BitVec.ofNat 32 n) := by simp only [imm, Op2.eval, h, ite_true]

/-- An immediate's encodability, decided by `arun`'s discharger. -/
theorem encodable_of_decide {v : BitVec 32} (h : encodable v = true) : encodable v = true := h

/-- Runs a block of the instructions the AES-GCM code uses. -/
macro "arun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, imm, addI, State.load32, store32_eq, State.load8, store8_eq,
    tO, uO, vO, rO, scrO, List.cons_append, List.nil_append, List.append_assoc, Option.map_some,
    gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg, z_setReg, c_setReg, gpr_subFlags, mem_subFlags,
    rd_subFlags, wr_subFlags, sp_subFlags, z_subFlags, c_subFlags, sp_store, gpr_store, rd_store, wr_store,
    mem_store, z_store, c_store, ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul, and_self, and_true, true_and, encodable_of_decide,
    eq_self_iff_true, $ts,*]) <;>
  try rfl)

/-- A buffer of `n` bytes at the 32-bit pointer `D` that the code may read,
apart from the state, `W` and the stack below `sp`. -/
structure DataOk (st w sp : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨State.addr D, n⟩] (s.rd ++ s.wr)
  lt32 : n < 2 ^ 32
  fit : D.toNat + n ≤ 2 ^ 32
  st : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr st, 80⟩
  w : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  stk : (VG.Proof.AesGcm.Arm.below sp).Disjoint ⟨State.addr D, n⟩

namespace DataOk

variable {st w sp : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesGcm.Arm.DataOk st w sp s D n)
include h

theorem lt : n < 2 ^ 64 := by have := h.fit; omega

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.Arm.DataOk st w sp s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- Byte `j` of the buffer, for `j < n`, as a 64-bit address. -/
theorem addr {j : Nat} (hj : j < n) : State.addr (D + BitVec.ofNat 32 j) = State.addr D + BitVec.ofNat 64 j :=
  addr_add (by have := h.fit; omega)

theorem toNat_add {j : Nat} (hj : j < n) : (D + BitVec.ofNat 32 j).toNat = D.toNat + j := by
  have := h.fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcm.Arm.DataOk st w sp s D k where
  rd := VG.Proof.AesGcm.Arm.covers_prefix h.rd hk
  lt32 := by have := h.lt32; omega
  fit := by have := h.fit; omega
  st := h.st.sub_left (Region.sub_prefix hk)
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- The `k` (at least one) bytes from `j` on. -/
theorem sub {j k : Nat} (hjk : j + k ≤ n) (hk : 0 < k) : VG.Proof.AesGcm.Arm.DataOk st w sp s (D + BitVec.ofNat 32 j) k := by
  have ha := h.addr (j := j) (by omega)
  have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 j, k⟩ ⟨State.addr D, n⟩ := Offset.sub_base _ hjk
  refine ⟨?_, by have := h.lt32; omega, ?_, ?_, ?_, ?_⟩
  · rw [ha]; exact VG.Proof.AesGcm.Arm.covers_off h.rd hjk h.lt
  · rw [h.toNat_add (by omega)]; have := h.fit; omega
  · rw [ha]; exact h.st.sub_left hs
  · rw [ha]; exact h.w.sub_left hs
  · rw [ha]; exact h.stk.sub_right hs

end DataOk

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

/-- The bytes at `p`, after writing `xs` at `p + o`: the first `o`, then `xs`. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (o : Nat) (xs : List Byte) (h : o + xs.length < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m (p + BitVec.ofNat 64 o) xs) p (o + xs.length) = bytesAt m p o ++ xs := by
  rw [VG.Proof.AesGcm.Arm.bytesAt_add]
  congr 1
  · simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact VG.WriteBytes.writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp [bytesAt])
    intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeBytes, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h₁, ite_true,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some]

theorem bytesAt_writeBytes_self (m : Mem) (p : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m p xs) p xs.length = xs := by
  have := VG.Proof.AesGcm.Arm.bytesAt_writeBytes m p 0 xs (by omega)
  simp only [Nat.zero_add, BitVec.add_zero] at this
  rw [this]; rfl

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- A write of `xs` at `q`, within `R`, keeps everything outside `R`. -/
theorem writeBytes_frame' (m : Mem) {q : Addr} {xs : List Byte} {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (VG.WriteBytes.writeBytes m q xs) :=
  VG.WriteBytes.writeBytes_frame m q xs (by rw [hn]; exact Region.contains_self _ _)

/-- The bytes at `p` after writing `xs` there: `xs`, then what was there. -/
theorem bytesAt_writeBytes_prefix (m : Mem) (p : Addr) (xs : List Byte) {n : Nat} (hn : xs.length ≤ n)
    (h : n < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m p xs) p n = xs ++ bytesAt m (p + BitVec.ofNat 64 xs.length) (n - xs.length) := by
  rw [show n = xs.length + (n - xs.length) by omega, VG.Proof.AesGcm.Arm.bytesAt_add, VG.Proof.AesGcm.Arm.bytesAt_writeBytes_self _ _ _ (by omega),
    Nat.add_sub_cancel_left]
  congr 1
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [VG.WriteBytes.writeBytes, BitVec.add_assoc, Offset.add_sub_cancel_left, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := xs.length) (by omega), Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  simp [show ¬ (xs.length + i < xs.length) by omega]

/-- Running a block with what is known of its result. -/
theorem WP.run {is : List Instr} {s : State} {Q R : State → Prop}
    (h : ∃ s', runBlock isa is s = some s' ∧ Q s') (hq : ∀ s', Q s' → R s') : WP isa (.block is) s R := by
  obtain ⟨s', h₁, h₂⟩ := h; exact WP.of_runBlock ⟨s', h₁, hq _ h₂⟩

theorem eval_eq' {s : State} {b : Bool} (h : s.z = b) : isa.eval .eq s = some b := by
  show VG.Arm.eval .eq s = _; rw [VG.Proof.MdStream.Arm.eval_eq, h]

theorem eval_ne' {s : State} {b : Bool} (h : s.z = b) : isa.eval .ne s = some !b := by
  show VG.Arm.eval .ne s = _; rw [VG.Proof.MdStream.Arm.eval_ne, h]

/-- `Z` after `cmp` of a register holding `n` with `k`. -/
theorem z_cmp {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := VG.Proof.MdStream.Arm.sub_beq ha hb

theorem z_cmp0 {a : Nat} (ha : a < 2 ^ 32) : (BitVec.ofNat 32 a == 0) = decide (a = 0) :=
  VG.Proof.MdStream.Arm.ofNat_beq_zero ha

theorem ofNat_sub32 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega)]
  omega

theorem ofNat_add32 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem toNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := VG.Proof.AesGcm.Arm.toNat_ofNat32 h

theorem and15 (x : BitVec 32) : x &&& BitVec.ofNat 32 15 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 15) (by decide),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr4 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 4 = BitVec.ofNat 32 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Loops`. -/
section

/-!
# AES-GCM on ARMv7: the byte loops

Untrusted: everything here is checked by Lean. `copyLoop` copies `r3` bytes
from `r1` to `r2`, and `xorLoop` XORs `r3` bytes at `r1` into those at `r2`,
a byte at a time through advancing pointers, counting `r3` down to zero
(`copyLoop_ok`, `xorLoop_ok`); the buffers do not overlap.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem bytesAt_succ (m : Mem) (p : Addr) (i : Nat) :
    bytesAt m p (i + 1) = bytesAt m p i ++ [m (p + BitVec.ofNat 64 i)] := by
  simp [bytesAt, List.range_succ]

/-- Byte `i` of a region `⟨p, n⟩`, `i < n`, is in it. -/
theorem in_of_covers {rs : List Region} {p : Addr} {n i : Nat} (h : Covers [⟨p, n⟩] rs) (hi : i < n)
    (hn : n < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 i) 1 :=
  h _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base p (by omega) (by omega)⟩

/-- What the loops need of the state: `n` (at least 1) bytes at the 32-bit
pointers `S` (read) and `D` (written). -/
structure LoopPre (s : State) (S D : BitVec 32) (n : Nat) : Prop where
  r1 : s.gpr .r1 = S
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = BitVec.ofNat 32 n
  pos : 1 ≤ n
  lt : n < 2 ^ 32
  fitS : S.toNat + n ≤ 2 ^ 32
  fitD : D.toNat + n ≤ 2 ^ 32
  rd : Covers [⟨State.addr S, n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨State.addr D, n⟩] s.wr
  disj : (⟨State.addr S, n⟩ : Region).Disjoint ⟨State.addr D, n⟩

/-- What the loops leave, but memory. -/
structure LoopOut (s : State) (S D : BitVec 32) (n : Nat) (s' : State) : Prop where
  r1 : s'.gpr .r1 = S + BitVec.ofNat 32 n
  r2 : s'.gpr .r2 = D + BitVec.ofNat 32 n
  r3 : s'.gpr .r3 = 0
  other : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem addr_i {P : BitVec 32} {n i : Nat} (hf : P.toNat + n ≤ 2 ^ 32) (hi : i < n) :
    State.addr (P + BitVec.ofNat 32 i) = State.addr P + BitVec.ofNat 64 i := addr_add (by omega)

theorem setWidth8_32 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem dec32 {n i : Nat} (hi : i < n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = BitVec.ofNat 32 (n - (i + 1)) := by
  rw [VG.Proof.AesGcm.Arm.ofNat_sub32 (by omega) (by omega)]; congr 1

theorem z_dec {n i : Nat} (hi : i < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - (i + 1)) == 0) = decide (i + 1 = n) := by
  rw [VG.Proof.AesGcm.Arm.z_cmp0 (by omega)]; congr 1; apply propext; omega

/-! ## `copyLoop` -/

abbrev copyBody : List Instr :=
  [.ldrb .r12 .r1 0, .strb .r12 .r2 0, addI .r1 .r1 1, addI .r2 .r2 1, .subs .r3 .r3 (imm 1)]

theorem copyStep_ok (s : State) {S D : BitVec 32} {i n : Nat} (hs : s.gpr .r1 = S + BitVec.ofNat 32 i)
    (hd : s.gpr .r2 = D + BitVec.ofNat 32 i) (hn : s.gpr .r3 = BitVec.ofNat 32 (n - i))
    (r : InRegions (s.rd ++ s.wr) (State.addr (S + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa VG.Proof.AesGcm.Arm.copyBody s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i)) (s.mem (State.addr (S + BitVec.ofNat 32 i))) ∧
      s'.gpr .r1 = S + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r2 = D + BitVec.ofNat 32 (i + 1) ∧
      s'.gpr .r3 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  refine ⟨_, by arun [hs, hd, hn, VG.Proof.AesGcm.Arm.add_ofNat_zero, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, VG.Proof.AesGcm.Arm.mem_subFlags, VG.Proof.AesGcm.Arm.mem_store, VG.Proof.AesGcm.Arm.setWidth8_32]
  · simp [gpr_setReg, hs, VG.Proof.AesGcm.Arm.add32_ofNat_assoc]
  · simp [gpr_setReg, hd, VG.Proof.AesGcm.Arm.add32_ofNat_assoc]
  · simp [gpr_setReg, hn]
  · simp [z_setReg, hn]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setReg, h₁, h₂, h₃, h₄]
  all_goals rfl

/-- The source byte `i` is not overwritten by the copy so far. -/
theorem src_kept {m : Mem} {S D : Addr} {n i : Nat} (hd : (⟨S, n⟩ : Region).Disjoint ⟨D, n⟩) (hi : i < n)
    (hn : n < 2 ^ 63) (xs : List Byte) (hxs : xs.length = i) :
    VG.WriteBytes.writeBytes m D xs (S + BitVec.ofNat 64 i) = m (S + BitVec.ofNat 64 i) :=
  (VG.WriteBytes.writeBytes_frame m D xs (R := ⟨D, i⟩) (by rw [hxs]; exact Region.contains_self _ _)) _
    fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd _ (Offset.contains_base S (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)

theorem copyLoop_ok (s : State) {S D : BitVec 32} {n : Nat} (h : VG.Proof.AesGcm.Arm.LoopPre s S D n) :
    WP isa copyLoop s fun s' => s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) n) ∧
      VG.Proof.AesGcm.Arm.LoopOut s S D n s' := by
  have hn32 : n < 2 ^ 32 := h.lt
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcm.Arm.copyBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r1 = S + BitVec.ofNat 32 i ∧
      t.gpr .r2 = D + BitVec.ofNat 32 i ∧ t.gpr .r3 = BitVec.ofNat 32 (n - i) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) i) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.r1, VG.Proof.AesGcm.Arm.add_ofNat_zero], by rw [h.r2, VG.Proof.AesGcm.Arm.add_ofNat_zero], by rw [h.r3]; rfl,
      by simp [bytesAt, VG.WriteBytes.writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r1, r2, r3, mem, g, rd, wr, sp⟩
  have aS := VG.Proof.AesGcm.Arm.addr_i h.fitS hi
  have aD := VG.Proof.AesGcm.Arm.addr_i h.fitD hi
  obtain ⟨t', run', mem', r1', r2', r3', z', g', rd', wr', sp'⟩ := VG.Proof.AesGcm.Arm.copyStep_ok t r1 r2 r3
    (by rw [rd, wr, aS]; exact VG.Proof.AesGcm.Arm.in_of_covers h.rd hi (by omega))
    (by rw [wr, aD]; exact VG.Proof.AesGcm.Arm.in_of_covers h.wr hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (bytesAt s.mem (State.addr S) i).length = i := by simp [bytesAt]
  have hmem : t'.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) (i + 1)) := by
    rw [mem', mem, aS, aD, VG.Proof.AesGcm.Arm.src_kept h.disj hi (by omega) _ hlen, VG.Proof.AesGcm.Arm.bytesAt_succ,
      VG.WriteBytes.writeBytes_snoc s.mem _ (bytesAt s.mem _ i) _ (by rw [hlen]; omega), hlen]
  have hz : t'.z = decide (i + 1 = n) := by rw [z', VG.Proof.AesGcm.Arm.dec32 hi hn32, VG.Proof.AesGcm.Arm.z_dec hi hn32]
  have gg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t'.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ => by rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  have ev : isa.eval .ne t' = some !decide (i + 1 = n) := VG.Proof.AesGcm.Arm.eval_ne' hz
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], ⟨by rw [r1', he], by rw [r2', he], ?_,
      fun r h₀ h₁ h₂ h₃ h₄ => gg r h₁ h₂ h₃ h₄, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩⟩
    rw [r3', VG.Proof.AesGcm.Arm.dec32 hi hn32, he, Nat.sub_self]; rfl
  · right
    refine ⟨by rw [ev]; simp [he], n - (i + 1), by omega, i + 1, rfl, by omega, r1', r2',
      by rw [r3', VG.Proof.AesGcm.Arm.dec32 hi hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

/-! ## `xorLoop` -/

abbrev xorBody : List Instr :=
  [.ldrb .r12 .r2 0, .ldrb .r0 .r1 0, .dp .eor .r12 .r12 (.reg .r0), .strb .r12 .r2 0,
    addI .r1 .r1 1, addI .r2 .r2 1, .subs .r3 .r3 (imm 1)]

theorem setWidth8_xor (a b : Byte) :
    ((a.setWidth 32 ^^^ b.setWidth 32 : BitVec 32)).setWidth 8 = a ^^^ b := by
  ext j hj; simp

theorem xorStep_ok (s : State) {S D : BitVec 32} {i n : Nat} (hs : s.gpr .r1 = S + BitVec.ofNat 32 i)
    (hd : s.gpr .r2 = D + BitVec.ofNat 32 i) (hn : s.gpr .r3 = BitVec.ofNat 32 (n - i))
    (r : InRegions (s.rd ++ s.wr) (State.addr (S + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa VG.Proof.AesGcm.Arm.xorBody s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i))
        (s.mem (State.addr (D + BitVec.ofNat 32 i)) ^^^ s.mem (State.addr (S + BitVec.ofNat 32 i))) ∧
      s'.gpr .r1 = S + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r2 = D + BitVec.ofNat 32 (i + 1) ∧
      s'.gpr .r3 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  have w' : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 i)) 1 := VG.Proof.AesGcm.Arm.in_left w
  refine ⟨_, by arun [hs, hd, hn, VG.Proof.AesGcm.Arm.add_ofNat_zero, r, w, w'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, VG.Proof.AesGcm.Arm.mem_subFlags, VG.Proof.AesGcm.Arm.mem_store, gpr_setReg, VG.Proof.AesGcm.Arm.gpr_store, ite_true, VG.Proof.AesGcm.Arm.setWidth8_xor]
  · simp [gpr_setReg, hs, VG.Proof.AesGcm.Arm.add32_ofNat_assoc]
  · simp [gpr_setReg, hd, VG.Proof.AesGcm.Arm.add32_ofNat_assoc]
  · simp [gpr_setReg, hn]
  · simp [z_setReg, hn]
  · intro r h₀ h₁ h₂ h₃ h₄; simp [gpr_setReg, h₀, h₁, h₂, h₃, h₄]
  all_goals rfl

/-- The bytes at `D` XORed with those at `S`. -/
def xorBytes (m : Mem) (D S : Addr) (n : Nat) : List Byte :=
  List.zipWith (· ^^^ ·) (bytesAt m D n) (bytesAt m S n)

theorem xorBytes_succ (m : Mem) (D S : Addr) (i : Nat) :
    VG.Proof.AesGcm.Arm.xorBytes m D S (i + 1) = VG.Proof.AesGcm.Arm.xorBytes m D S i ++ [m (D + BitVec.ofNat 64 i) ^^^ m (S + BitVec.ofNat 64 i)] := by
  simp [VG.Proof.AesGcm.Arm.xorBytes, VG.Proof.AesGcm.Arm.bytesAt_succ, List.zipWith_append, Cmac.bytesAt_length]

theorem length_xorBytes (m : Mem) (D S : Addr) (n : Nat) : (VG.Proof.AesGcm.Arm.xorBytes m D S n).length = n := by
  simp [VG.Proof.AesGcm.Arm.xorBytes, Cmac.bytesAt_length]

/-- Byte `i` of the destination, not yet written. -/
theorem dst_kept {m : Mem} {D : Addr} {n i : Nat} (hi : i < n) (hn : n < 2 ^ 63) (xs : List Byte)
    (hxs : xs.length = i) : VG.WriteBytes.writeBytes m D xs (D + BitVec.ofNat 64 i) = m (D + BitVec.ofNat 64 i) := by
  simp only [VG.WriteBytes.writeBytes, hxs, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.lt_irrefl, ite_false]

theorem xorLoop_ok (s : State) {S D : BitVec 32} {n : Nat} (h : VG.Proof.AesGcm.Arm.LoopPre s S D n) :
    WP isa xorLoop s fun s' =>
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (VG.Proof.AesGcm.Arm.xorBytes s.mem (State.addr D) (State.addr S) n) ∧
      VG.Proof.AesGcm.Arm.LoopOut s S D n s' := by
  have hn32 : n < 2 ^ 32 := h.lt
  refine WP.loop (M := isa) (body := .block VG.Proof.AesGcm.Arm.xorBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = n - i ∧ i < n ∧ t.gpr .r1 = S + BitVec.ofNat 32 i ∧
      t.gpr .r2 = D + BitVec.ofNat 32 i ∧ t.gpr .r3 = BitVec.ofNat 32 (n - i) ∧
      t.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (VG.Proof.AesGcm.Arm.xorBytes s.mem (State.addr D) (State.addr S) i) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp) ?_ (n - 0) _
    ⟨0, rfl, h.pos, by rw [h.r1, VG.Proof.AesGcm.Arm.add_ofNat_zero], by rw [h.r2, VG.Proof.AesGcm.Arm.add_ofNat_zero], by rw [h.r3]; rfl,
      by simp [VG.Proof.AesGcm.Arm.xorBytes, bytesAt, VG.WriteBytes.writeBytes_nil], fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro k t ⟨i, rfl, hi, r1, r2, r3, mem, g, rd, wr, sp⟩
  have aS := VG.Proof.AesGcm.Arm.addr_i h.fitS hi
  have aD := VG.Proof.AesGcm.Arm.addr_i h.fitD hi
  obtain ⟨t', run', mem', r1', r2', r3', z', g', rd', wr', sp'⟩ := VG.Proof.AesGcm.Arm.xorStep_ok t r1 r2 r3
    (by rw [rd, wr, aS]; exact VG.Proof.AesGcm.Arm.in_of_covers h.rd hi (by omega))
    (by rw [wr, aD]; exact VG.Proof.AesGcm.Arm.in_of_covers h.wr hi (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen := VG.Proof.AesGcm.Arm.length_xorBytes s.mem (State.addr D) (State.addr S) i
  have hmem : t'.mem = VG.WriteBytes.writeBytes s.mem (State.addr D) (VG.Proof.AesGcm.Arm.xorBytes s.mem (State.addr D) (State.addr S) (i + 1)) := by
    rw [mem', mem, aS, aD, VG.Proof.AesGcm.Arm.src_kept h.disj hi (by omega) _ hlen, VG.Proof.AesGcm.Arm.dst_kept hi (by omega) _ hlen, VG.Proof.AesGcm.Arm.xorBytes_succ,
      VG.WriteBytes.writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have hz : t'.z = decide (i + 1 = n) := by rw [z', VG.Proof.AesGcm.Arm.dec32 hi hn32, VG.Proof.AesGcm.Arm.z_dec hi hn32]
  have gg : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t'.gpr r = s.gpr r :=
    fun r h₀ h₁ h₂ h₃ h₄ => by rw [g' r h₀ h₁ h₂ h₃ h₄, g r h₀ h₁ h₂ h₃ h₄]
  have ev : isa.eval .ne t' = some !decide (i + 1 = n) := VG.Proof.AesGcm.Arm.eval_ne' hz
  by_cases he : i + 1 = n
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], ⟨by rw [r1', he], by rw [r2', he], ?_, gg,
      by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩⟩
    rw [r3', VG.Proof.AesGcm.Arm.dec32 hi hn32, he, Nat.sub_self]; rfl
  · right
    refine ⟨by rw [ev]; simp [he], n - (i + 1), by omega, i + 1, rfl, by omega, r1', r2',
      by rw [r3', VG.Proof.AesGcm.Arm.dec32 hi hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Blocks`. -/
section

/-!
# AES-GCM on ARMv7: small blocks shared by the pieces

Untrusted: everything here is checked by Lean. `cmp r, #0` (`cmp0_ok`), and
`minLen`: `r3 := min (16 - r6, r5)`, from the carry of a comparison
(`minLen_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm

/-- `cmp r, #0` sets `Z` iff `r` holds 0. -/
theorem cmp0_ok (s : State) (r : Reg) {n : Nat} (h : s.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    ∃ s', runBlock isa [.cmp r (imm 0)] s = some s' ∧ s'.z = decide (n = 0) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.AesGcm.Arm.z_subFlags, h]; rw [VG.Proof.AesGcm.Arm.z_cmp hn (by decide)]
  all_goals rfl

/-- `cmp r, #k`. -/
theorem cmpk_ok (s : State) (r : Reg) {n k : Nat} (h : s.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32)
    (hk : k < 2 ^ 32) (he : encodable (BitVec.ofNat 32 k) = true) :
    ∃ s', runBlock isa [.cmp r (imm k)] s = some s' ∧ s'.z = decide (n = k) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [he], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.AesGcm.Arm.z_subFlags, h]; rw [VG.Proof.AesGcm.Arm.z_cmp hn hk]
  all_goals rfl

/-- What a block that keeps everything but some registers leaves. -/
structure Keeps (s s' : State) : Prop where
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : VG.Proof.AesGcm.Arm.Keeps s₁ s₂) (h₂ : VG.Proof.AesGcm.Arm.Keeps s₂ s₃) : VG.Proof.AesGcm.Arm.Keeps s₁ s₃ :=
  ⟨h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Keeps.refl (s : State) : VG.Proof.AesGcm.Arm.Keeps s s := ⟨rfl, rfl, rfl, rfl⟩

theorem adc_c (b : Bool) : (0 : BitVec 32) + BitVec.ofNat 32 0 + (if b = true then 1 else 0) =
    if b then 1 else 0 := by cases b <;> rfl

/-- `r3 := min (16 - r6, r5)`. -/
theorem minLen_ok (s : State) {o n : Nat} (h6 : s.gpr .r6 = BitVec.ofNat 32 o)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (ho : o ≤ 16) (hn : n < 2 ^ 32) :
    WP isa minLen s fun s' => s'.gpr .r3 = BitVec.ofNat 32 (min (16 - o) n) ∧
      (∀ r, r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ VG.Proof.AesGcm.Arm.Keeps s s' := by
  obtain ⟨s₁, run₁, h₁⟩ : ∃ s₁, runBlock isa [.mov .r3 (imm 16), .dp .sub .r3 .r3 (.reg .r6), .cmp .r5 (.reg .r3),
      .mov .r12 (imm 0), .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r3 = BitVec.ofNat 32 (16 - o) ∧ s₁.z = !decide (16 - o ≤ n) ∧
      (∀ r, r ≠ .r3 → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ VG.Proof.AesGcm.Arm.Keeps s s₁ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h6, VG.Proof.AesGcm.Arm.ofNat_sub32 ho (by decide)]
    · simp only [VG.Proof.AesGcm.Arm.z_subFlags, VG.Proof.AesGcm.Arm.c_subFlags, gpr_setReg, z_setReg, c_setReg, ite_true, ite_false, reduceCtorEq,
        h5, h6, VG.Proof.AesGcm.Arm.ofNat_sub32 ho (by decide), VG.Proof.AesGcm.Arm.toNat32 hn, VG.Proof.AesGcm.Arm.toNat32 (show 16 - o < 2 ^ 32 by omega)]
      cases decide (16 - o ≤ n) <;> rfl
    · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hr3, hz, hg, hk⟩ := h₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (!decide (16 - o ≤ n)) (VG.Proof.AesGcm.Arm.eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · refine WP.run (Q := fun s' => s' = s₁.setReg .r3 (s₁.gpr .r5)) ⟨_, by arun [], rfl⟩ fun s' hs' => ?_
    subst hs'
    refine ⟨?_, fun r h₁ h₂ => ?_, hk.trans ⟨rfl, rfl, rfl, rfl⟩⟩
    · rw [gpr_setReg_self, hg .r5 (by decide) (by decide), h5]
      simp at ht; rw [Nat.min_eq_right (by omega)]
    · simp only [gpr_setReg, h₁, ite_false]; exact hg r h₁ h₂
  · refine WP.block_nil ⟨?_, hg, hk⟩
    simp at hf; rw [hr3, Nat.min_eq_left (by omega)]

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Ghash1`. -/
section

/-!
# AES-GCM on ARMv7: GHASH over blocks of the state, `T` or the data

Untrusted: everything here is checked by Lean. `ghCall_ok` is the frame of a
call of `vg_ghash` from a state whose registers are its arguments (the hash
subkey at `ctx + 240`, the accumulator at `st + yo`, the working space at
`W + 512`), and `ghash1 yo b o` continues the accumulator over the block at
`P = b + o` (`ghash1_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-- What a call of `vg_ghash` from `s` leaves in `s'`, for the accumulator
at `Y`, the working space at `W + 512` and the data `ds` (as blocks). -/
structure GhOut (s : State) (c w sp : BitVec 32) (Y : Addr) (ds : List Block) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  spk : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, VG.Proof.AesGcm.Arm.below sp] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem (State.addr c + BitVec.ofNat 64 240)) (blockAt s.mem Y) ds

theorem GhOut.env {s s' : State} {c st w sp k7 k8 : BitVec 32} {Y : Addr} {ds : List Block}
    (h : VG.Proof.AesGcm.Arm.GhOut s c w sp Y ds s') (he : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s) : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s' :=
  he.of_saved h.saved h.spk h.rd h.wr

theorem blocksAt_one (m : Mem) (p : Addr) : blocksAt m p 1 = [blockAt m p] := by
  simp [blocksAt]

/-- The arguments of a call, from a state whose registers are its arguments,
for `n` blocks at the 32-bit pointer `P`. -/
theorem ghCall_mk {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s) {P : BitVec 32} {n : Nat}
    (h0 : s.gpr .r0 = c + BitVec.ofNat 32 240) (h1 : s.gpr .r1 = st + BitVec.ofNat 32 yo)
    (h2 : s.gpr .r2 = P) (h3 : s.gpr .r3 = BitVec.ofNat 32 n) (h12 : s.gpr .r12 = w + BitVec.ofNat 32 512)
    (hfit : P.toNat + 16 * n ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16 * n⟩)
    (hpw : (⟨State.addr P, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (VG.Proof.AesGcm.Arm.below sp).Disjoint ⟨State.addr P, 16 * n⟩) (hpr : Covers [⟨State.addr P, 16 * n⟩] (s.rd ++ s.wr)) :
    VG.Proof.AesGcm.Arm.GhCall s (c + BitVec.ofNat 32 240) (st + BitVec.ofNat 32 yo) P (w + BitVec.ofNat 32 512) n := by
  have eH := L.cA (d := 240) (by decide)
  have eY := L.stA (d := yo) (by omega)
  have eS := L.wA (d := 512) (by decide)
  have hk := he.sp
  refine ⟨h0, h1, h2, h3, h12, by rw [hk]; exact L.sp8, by rw [L.cN (by decide)]; have := L.cw; omega,
    by rw [L.stN (by omega)]; have := L.sw; omega, hfit, by rw [L.wN (by decide)]; have := L.ww; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [eH, eY, eS, hk]
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_w (by decide) (by decide)
  · exact hpy
  · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact hpw
  · exact L.stk_ctx (by decide)
  · exact L.stk_st (by omega)
  · exact hpk
  · exact L.stk_w (by decide)
  · exact VG.Proof.AesGcm.Arm.covers_cons (he.perm.ctxC (by decide)) hpr
  · exact VG.Proof.AesGcm.Arm.covers_cons (he.perm.stC (by omega)) (he.perm.wC (by decide))

/-- The call itself, from a state whose registers are its arguments, for
`n` blocks at the 32-bit pointer `P`. -/
theorem ghCall_ok {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s) {P : BitVec 32} {n : Nat}
    (h0 : s.gpr .r0 = c + BitVec.ofNat 32 240) (h1 : s.gpr .r1 = st + BitVec.ofNat 32 yo)
    (h2 : s.gpr .r2 = P) (h3 : s.gpr .r3 = BitVec.ofNat 32 n) (h12 : s.gpr .r12 = w + BitVec.ofNat 32 512)
    (hfit : P.toNat + 16 * n ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16 * n⟩)
    (hpw : (⟨State.addr P, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (VG.Proof.AesGcm.Arm.below sp).Disjoint ⟨State.addr P, 16 * n⟩) (hpr : Covers [⟨State.addr P, 16 * n⟩] (s.rd ++ s.wr)) :
    WP isa ghFrame s (VG.Proof.AesGcm.Arm.GhOut s c w sp (State.addr st + BitVec.ofNat 64 yo) (blocksAt s.mem (State.addr P) n)) := by
  have eH := L.cA (d := 240) (by decide)
  have eY := L.stA (d := yo) (by omega)
  have eS := L.wA (d := 512) (by decide)
  have hc := VG.Proof.AesGcm.Arm.ghCall_mk L hyo he h0 h1 h2 h3 h12 hfit hpy hpw hpk hpr
  refine WP.mono (VG.Proof.AesGcm.Arm.gh_call hc) fun s' h => ⟨h.rd, h.wr, h.sp, h.saved, ?_, ?_⟩
  · have f := h.frame; rw [eY, eS, he.sp] at f; exact f
  · have o := h.out; rw [eH, eY] at o; exact o

/-- The arguments of `ghash1`. -/
theorem ghArgs_ok {c st w sp k7 k8 : BitVec 32} {s : State} (he : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s) (yo : Nat) (b : Reg) (o : Nat)
    (hb : b = .r10 ∨ b = .r11) (hyo : encodable (BitVec.ofNat 32 yo) = true)
    (ho : encodable (BitVec.ofNat 32 o) = true) :
    ∃ s', runBlock isa [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r2 b o, .mov .r3 (imm 1),
        addI .r12 .r11 scrO] s = some s' ∧
      s'.gpr .r0 = c + BitVec.ofNat 32 240 ∧ s'.gpr .r1 = st + BitVec.ofNat 32 yo ∧
      s'.gpr .r2 = s.gpr b + BitVec.ofNat 32 o ∧ s'.gpr .r3 = BitVec.ofNat 32 1 ∧
      s'.gpr .r12 = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ VG.Proof.AesGcm.Arm.Keeps s s' := by
  have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  rcases hb with rfl | rfl
  all_goals
    refine ⟨_, by arun [hyo, ho], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h9]
    · simp [gpr_setReg, h10]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
    · simp [gpr_setReg, h11]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩

/-- `ghash1 yo b o`, for the block at `P = b + o`. -/
theorem ghash1_ok {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
    {s : State} (he : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s) (b : Reg) (o : Nat) (hb : b = .r10 ∨ b = .r11)
    (ho : encodable (BitVec.ofNat 32 o) = true) {P : BitVec 32}
    (hP : s.gpr b + BitVec.ofNat 32 o = P) (hfit : P.toNat + 16 ≤ 2 ^ 32)
    (hpy : (⟨State.addr st + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨State.addr P, 16⟩)
    (hpw : (⟨State.addr P, 16⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 512, 256⟩)
    (hpk : (VG.Proof.AesGcm.Arm.below sp).Disjoint ⟨State.addr P, 16⟩) (hpr : Covers [⟨State.addr P, 16⟩] (s.rd ++ s.wr)) :
    WP isa (ghash1 yo b o) s (VG.Proof.AesGcm.Arm.GhOut s c w sp (State.addr st + BitVec.ofNat 64 yo) [blockAt s.mem (State.addr P)]) := by
  obtain ⟨s₁, run₁, h0, h1, h2, h3, h12, hkeep, hk⟩ := VG.Proof.AesGcm.Arm.ghArgs_ok he yo b o hb
    (by rcases hyo with rfl | rfl <;> decide) ho
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide))
    hk.sp hk.rd hk.wr
  refine WP.mono (VG.Proof.AesGcm.Arm.ghCall_ok L hyo he₁ (P := P) (n := 1) h0 h1 (by rw [h2, hP]) h3 h12 (by omega)
    (by simpa using hpy) (by simpa using hpw) (by simpa using hpk)
    (by rw [hk.rd, hk.wr]; simpa using hpr)) fun s' h => ?_
  exact ⟨h.rd.trans hk.rd, h.wr.trans hk.wr, h.spk.trans hk.sp,
    fun r hr hl => by
      rw [h.saved r hr hl]
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hl | exact hkeep _ (by decide) (by decide) (by decide) (by decide) (by decide),
    hk.mem ▸ h.frame, by rw [h.out, VG.Proof.AesGcm.Arm.blocksAt_one, hk.mem]⟩

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Absorb`. -/
section

/-!
# AES-GCM on ARMv7: GHASH absorbing a piece (`absorb`)

Untrusted: everything here is checked by Lean. `absorb yo` absorbs the
`r5` bytes at `r4` into GHASH, with the accumulator at `St + yo` and the
`r6` buffered bytes at `St + 32` (`absorb_ok`): it fills the buffer
(`headPre_ok`, `head_ok`), absorbs whole blocks (`whole_ok`) and buffers the
rest (`tail_ok`), by the steps of `Proof/Gcm/Stream.lean`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Proof.Gcm (Absorbed)

/-- The regions `absorb` writes. -/
abbrev absFrame (st w sp : BitVec 32) (yo : Nat) : List Region :=
  [⟨State.addr st + BitVec.ofNat 64 yo, 16⟩, ⟨State.addr st + BitVec.ofNat 64 32, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, VG.Proof.AesGcm.Arm.below sp]

/-- Before `absorb yo`: GHASH has absorbed `x` (with hash subkey `H`), and
`r4`, `r5`, `r6` hold the data, its length and `len(x) mod 16`. -/
structure AbsIn (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x : List Byte) (D : BitVec 32) (n : Nat)
    (s : State) : Prop where
  env : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s
  r4 : s.gpr .r4 = D
  r5 : s.gpr .r5 = BitVec.ofNat 32 n
  r6 : s.gpr .r6 = BitVec.ofNat 32 (x.length % 16)
  data : VG.Proof.AesGcm.Arm.DataOk st w sp s D n
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H

/-- Part of the way: `j` bytes absorbed, from `m₀`. -/
structure AbsMid (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x : List Byte) (D : BitVec 32) (n : Nat)
    (m₀ : Mem) (j : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s
  le : j ≤ n
  r4 : s.gpr .r4 = D + BitVec.ofNat 32 j
  r5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)
  data : VG.Proof.AesGcm.Arm.DataOk st w sp s D n
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x →
    Absorbed s.mem (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H
      (x ++ bytesAt m₀ (State.addr D) j)
  whole : n - j = 0 ∨ (x.length + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.Arm.absFrame st w sp yo) m₀ s.mem

/-- After: everything absorbed, from `x₀` absorbed in `m₀` to `x`. -/
structure AbsOut (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s
  abs : Absorbed m₀ (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x
  frame : Frame (VG.Proof.AesGcm.Arm.absFrame st w sp yo) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L in
/-- The data is apart from what `absorb` writes. -/
theorem data_absFrame {s : State} {D : BitVec 32} {n : Nat} (hd : VG.Proof.AesGcm.Arm.DataOk st w sp s D n) :
    ∀ r ∈ VG.Proof.AesGcm.Arm.absFrame st w sp yo, (⟨State.addr D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by omega))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

/-- The context is apart from what `absorb` writes. -/
theorem ctx_absFrame : ∀ r ∈ VG.Proof.AesGcm.Arm.absFrame st w sp yo,
    (⟨State.addr c + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_st (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

omit L hyo in
/-- A write within the buffer is within what `absorb` writes. -/
theorem buf_absFrame {m m' : Mem} {o k : Nat} (h : Frame [⟨State.addr st + BitVec.ofNat 64 (32 + o), k⟩] m m')
    (hk : o + k ≤ 16) : Frame (VG.Proof.AesGcm.Arm.absFrame st w sp yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by omega) (by omega)⟩

omit L hyo in
theorem gh_absFrame {m m' : Mem} (h : Frame [⟨State.addr st + BitVec.ofNat 64 yo, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, VG.Proof.AesGcm.Arm.below sp] m m') : Frame (VG.Proof.AesGcm.Arm.absFrame st w sp yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

end

/-- After `headPre`: `k = min (16 - o, n)` bytes copied into the buffer, the
arguments advanced, and `Z` set iff the buffer is full. -/
structure HeadMid (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x : List Byte) (D : BitVec 32) (n : Nat)
    (m₀ : Mem) (k : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s
  kmin : k = min (16 - x.length % 16) n
  k1 : 1 ≤ k
  k16 : x.length % 16 + k ≤ 16
  kn : k ≤ n
  r4 : s.gpr .r4 = D + BitVec.ofNat 32 (k)
  r5 : s.gpr .r5 = BitVec.ofNat 32 (n - k)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (x.length % 16 + k)
  z : s.z = decide (x.length % 16 + k = 16)
  data : VG.Proof.AesGcm.Arm.DataOk st w sp s D n
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  buf : bytesAt s.mem (State.addr st + BitVec.ofNat 64 32) (x.length % 16 + k) =
    bytesAt m₀ (State.addr st + BitVec.ofNat 64 32) (x.length % 16) ++
      bytesAt m₀ (State.addr D) (k)
  hY : blockAt s.mem (State.addr st + BitVec.ofNat 64 yo) = blockAt m₀ (State.addr st + BitVec.ofNat 64 yo)
  fw : Frame [⟨State.addr st + BitVec.ofNat 64 (32 + x.length % 16), k⟩] m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- Filling the buffer: `minLen`, the copy and the comparison with 16. -/
theorem headPre_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.AbsIn c st w sp k7 k8 yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa headPre s (fun s' => ∃ k, VG.Proof.AesGcm.Arm.HeadMid c st w sp k7 k8 yo H x D n s.mem k s') := by
  have hlt : x.length % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn32 : n < 2 ^ 32 := h.data.lt32
  have he := h.env
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.minLen_ok s h.r6 h.r5 (by omega) hn32) fun s₁ ⟨h3, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - x.length % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h3
  have hk1 : 1 ≤ k := by omega
  have hk16 : x.length % 16 + k ≤ 16 := by omega
  have hkn : k ≤ n := by omega
  obtain ⟨s₂, run₂, h1, h2, h4, h5, h6, h3', hg₂, hk₂⟩ : ∃ s₂, runBlock isa [addI .r2 .r10 32,
      .dp .add .r2 .r2 (.reg .r6), .mov .r1 (.reg .r4), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3),
      .dp .add .r6 .r6 (.reg .r3)] s₁ = some s₂ ∧
      s₂.gpr .r1 = D ∧ s₂.gpr .r2 = st + BitVec.ofNat 32 (32 + x.length % 16) ∧
      s₂.gpr .r4 = D + BitVec.ofNat 32 k ∧ s₂.gpr .r5 = BitVec.ofNat 32 (n - k) ∧
      s₂.gpr .r6 = BitVec.ofNat 32 (x.length % 16 + k) ∧ s₂.gpr .r3 = BitVec.ofNat 32 k ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧ VG.Proof.AesGcm.Arm.Keeps s₁ s₂ := by
    have e10 := hg .r10 (by decide) (by decide)
    have e4 := hg .r4 (by decide) (by decide)
    have e5 := hg .r5 (by decide) (by decide)
    have e6 := hg .r6 (by decide) (by decide)
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e4, h.r4]
    · simp [gpr_setReg, e10, e6, he.r10, h.r6, VG.Proof.AesGcm.Arm.add32_ofNat_assoc]
    · simp [gpr_setReg, e4, h.r4, h3]
    · simp [gpr_setReg, e5, h.r5, h3, VG.Proof.AesGcm.Arm.ofNat_sub32 hkn hn32]
    · simp [gpr_setReg, e6, h.r6, h3, VG.Proof.AesGcm.Arm.ofNat_add32]
    · simp [gpr_setReg, h3]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hk₂' := hk.trans hk₂
  have eB : State.addr (st + BitVec.ofNat 32 (32 + x.length % 16)) =
      State.addr st + BitVec.ofNat 64 (32 + x.length % 16) := L.stA (by omega)
  have lp : VG.Proof.AesGcm.Arm.LoopPre s₂ D (st + BitVec.ofNat 32 (32 + x.length % 16)) k := by
    refine ⟨h1, h2, h3', hk1, by omega, by have := h.data.fit; omega,
      by rw [L.stN (by omega)]; have := L.sw; omega, ?_, ?_, ?_⟩
    · rw [hk₂'.rd, hk₂'.wr]; exact (h.data.take hkn).rd
    · rw [hk₂'.wr, eB]; exact he.perm.stC (by omega)
    · rw [eB]; exact (h.data.take hkn).st.sub_right (Lay.stSub (by omega))
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_)
  rw [eB, hk₂'.mem] at hm₃
  obtain ⟨s₄, run₄, hz₄, hg₄, hk₄⟩ := VG.Proof.AesGcm.Arm.cmpk_ok s₃ .r6 (n := x.length % 16 + k) (k := 16)
    (by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h6]) (by omega)
    (by decide) (by decide)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₄.gpr r = s₂.gpr r :=
    fun r a b c d e => by rw [hg₄, lo.other r a b c d e]
  -- The bytes copied, and the buffer.
  have hdk := VG.Proof.AesGcm.Arm.length_bytesAt s.mem (State.addr D) k
  have fw : Frame [⟨State.addr st + BitVec.ofNat 64 (32 + x.length % 16), k⟩] s.mem s₄.mem := by
    rw [hk₄.1, hm₃]; exact VG.Proof.AesGcm.Arm.writeBytes_frame' _ hdk
  refine ⟨k, he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), hg _ (by decide) (by decide)])
      (by rw [hk₄.2.2.2, lo.sp, hk₂'.sp]) (by rw [hk₄.2.1, lo.rd, hk₂'.rd]) (by rw [hk₄.2.2.1, lo.wr, hk₂'.wr]),
    hk'.symm, hk1, hk16, hkn, ?_, ?_, ?_, hz₄, h.data.of_eq (by rw [hk₄.2.1, lo.rd, hk₂'.rd]) (by rw [hk₄.2.2.1, lo.wr, hk₂'.wr]),
    ?_, ?_, ?_, fw⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h4]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h5]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h6]
  · rw [VG.Proof.AesGcm.Arm.blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_st (by decide) (by omega), h.hH]
  · rw [hk₄.1, hm₃, show State.addr st + BitVec.ofNat 64 (32 + x.length % 16) =
        State.addr st + BitVec.ofNat 64 32 + BitVec.ofNat 64 (x.length % 16) from (VG.Proof.AesGcm.Arm.add_ofNat_assoc _ _ _).symm]
    have := VG.Proof.AesGcm.Arm.bytesAt_writeBytes s.mem (State.addr st + BitVec.ofNat 64 32) (x.length % 16)
      (bytesAt s.mem (State.addr D) k) (by rw [hdk]; omega)
    rwa [hdk] at this
  · exact VG.Proof.AesGcm.Arm.blockAt_frame fw fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by omega)) (by omega) (by omega)

end

section
variable {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- After `headPre`: the buffer absorbed if full. -/
theorem headPost_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {m₀ : Mem} {k : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.HeadMid c st w sp k7 k8 yo H x D n m₀ k s) :
    WP isa (.ite .eq (ghash1 yo .r10 32) (.block [])) s
      (fun s' => ∃ j, j = k ∧ VG.Proof.AesGcm.Arm.AbsMid c st w sp k7 k8 yo H x D n m₀ j s') := by
  have he := h.env
  have hk1 := h.k1; have hk16 := h.k16; have hkn := h.kn; have hkm := h.kmin
  have hdk := VG.Proof.AesGcm.Arm.length_bytesAt m₀ (State.addr D) k
  refine WP.ite (decide (x.length % 16 + k = 16)) (VG.Proof.AesGcm.Arm.eval_eq' h.z) (fun ht => ?_) (fun hf => ?_)
  · -- The buffer is full: absorbed.
    have h16 : x.length % 16 + k = 16 := by simpa using ht
    refine WP.mono (VG.Proof.AesGcm.Arm.ghash1_ok L hyo he .r10 32 (.inl rfl) (by decide) (P := st + BitVec.ofNat 32 32)
      (by rw [he.r10]) (by rw [L.stN (by decide)]; have := L.sw; omega) ?_ ?_ ?_ ?_) fun s₅ g => ?_
    · rw [L.stA (by decide)]; exact Lay.st_st (.inl (by omega)) (by omega) (by decide)
    · rw [L.stA (by decide)]; exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
    · rw [L.stA (by decide)]; exact L.stk_st (by decide)
    · rw [L.stA (by decide)]; exact VG.Proof.AesGcm.Arm.covers_left (he.perm.stC (by decide))
    refine ⟨k, rfl, g.env he, hkn, by rw [g.saved _ (by decide) (by decide)]; exact h.r4,
      by rw [g.saved _ (by decide) (by decide)]; exact h.r5, h.data.of_eq g.rd g.wr, ?_, ?_, .inr (by omega), ?_⟩
    · rw [VG.Proof.AesGcm.Arm.blockAt_frame g.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega)
        · exact L.ctx_w (by decide) (by decide)
        · exact (L.stk_ctx (by decide)).symm, h.hH]
    · intro ha
      refine Proof.Gcm.absorb_complete ha (by rw [hdk]; exact h16)
        (B := bytesAt s.mem (State.addr st + BitVec.ofNat 64 32) 16) ?_ ?_
      · rw [← h16, h.buf, ha.2]
      · rw [g.out, h.hY, h.hH, L.stA (by decide)]; rfl
    · exact (VG.Proof.AesGcm.Arm.buf_absFrame (yo := yo) (w := w) (sp := sp) h.fw hk16).trans (VG.Proof.AesGcm.Arm.gh_absFrame g.frame)
  · -- Not full: the data is used up.
    have h16 : x.length % 16 + k < 16 := by simp at hf; omega
    refine WP.block_nil ⟨k, rfl, he, hkn, h.r4, h.r5, h.data, h.hH, fun ha => ?_, .inl (by omega),
      VG.Proof.AesGcm.Arm.buf_absFrame (yo := yo) (w := w) (sp := sp) h.fw hk16⟩
    exact Proof.Gcm.absorb_fill ha (by rw [hdk]; exact h16) h.hY (by rw [hdk]; exact h.buf)

/-- Filling the buffer. -/
theorem head_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.AbsIn c st w sp k7 k8 yo H x D n s) (hn : n ≠ 0) (ho : x.length % 16 ≠ 0) :
    WP isa (absorbHead yo) s (fun s' => ∃ j, j = min (16 - x.length % 16) n ∧
      VG.Proof.AesGcm.Arm.AbsMid c st w sp k7 k8 yo H x D n s.mem j s') :=
  WP.seq (WP.mono (VG.Proof.AesGcm.Arm.headPre_ok L hyo h hn ho) fun _ ⟨_, hm⟩ =>
    WP.mono (VG.Proof.AesGcm.Arm.headPost_ok L hyo hm) fun _ ⟨j, hj, h'⟩ => ⟨j, hj.trans hm.kmin, h'⟩)

end

section
variable {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L hyo in
/-- The split of the rest into whole blocks and the last bytes. -/
theorem split_ok {s : State} {D : BitVec 32} {n j : Nat} (hj : j ≤ n) (hn : n < 2 ^ 32)
    (h4 : s.gpr .r4 = D + BitVec.ofNat 32 j) (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)) :
    ∃ s', runBlock isa splitWhole s = some s' ∧
      s'.gpr .r2 = D + BitVec.ofNat 32 j ∧ s'.gpr .r3 = BitVec.ofNat 32 ((n - j) / 16) ∧
      s'.gpr .r4 = D + BitVec.ofNat 32 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .r5 = BitVec.ofNat 32 (n - (j + 16 * ((n - j) / 16))) ∧
      s'.z = decide ((n - j) / 16 = 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ VG.Proof.AesGcm.Arm.Keeps s s' := by
  have hand := VG.Proof.AesGcm.Arm.and15 (BitVec.ofNat 32 (n - j))
  rw [VG.Proof.AesGcm.Arm.toNat32 (by omega)] at hand
  have hsub : BitVec.ofNat 32 (n - j) - BitVec.ofNat 32 ((n - j) % 16) = BitVec.ofNat 32 (16 * ((n - j) / 16)) := by
    rw [VG.Proof.AesGcm.Arm.ofNat_sub32 (Nat.mod_le _ _) (by omega)]; congr 1; omega
  refine ⟨_, by simp only [splitWhole]; arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h4]
  · simp [gpr_setReg, h5, VG.Proof.AesGcm.Arm.shr4 (show n - j < 2 ^ 32 by omega)]
  · simp only [gpr_setReg, VG.Proof.AesGcm.Arm.gpr_subFlags, ite_true, ite_false, reduceCtorEq, h4, h5, hand, hsub, VG.Proof.AesGcm.Arm.add32_ofNat_assoc]
  · simp only [gpr_setReg, VG.Proof.AesGcm.Arm.gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, hand]
    congr 1; omega
  · simp only [VG.Proof.AesGcm.Arm.z_subFlags, gpr_setReg, VG.Proof.AesGcm.Arm.gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, VG.Proof.AesGcm.Arm.shr4 (show n - j < 2 ^ 32 by omega)]
    rw [VG.Proof.AesGcm.Arm.z_cmp (by omega) (by decide)]
  · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The whole blocks. -/
theorem whole_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.AbsMid c st w sp k7 k8 yo H x D n m₀ j s) (hm₀ : bytesAt s.mem (State.addr D) n = bytesAt m₀ (State.addr D) n) :
    WP isa (absorbWhole yo) s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧
      VG.Proof.AesGcm.Arm.AbsMid c st w sp k7 k8 yo H x D n m₀ j' s' ∧ n - j' < 16) := by
  have hn' := h.data.lt32
  have he := h.env
  obtain ⟨s₁, run₁, h2, h3, h4, h5, hz, hg₁, hk₁⟩ := VG.Proof.AesGcm.Arm.split_ok h.le hn' h.r4 h.r5
  generalize hnb : (n - j) / 16 = nb at h3 h4 h5 hz
  have h16 : 16 * nb ≤ n - j := by omega
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) hk₁.sp hk₁.rd hk₁.wr
  have hd₁ : VG.Proof.AesGcm.Arm.DataOk st w sp s₁ D n := h.data.of_eq hk₁.rd hk₁.wr
  refine WP.ite (decide (nb = 0)) (VG.Proof.AesGcm.Arm.eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, by omega, ⟨he₁, h.le, by rw [h4]; rfl, by rw [h5]; rfl, hd₁, by rw [hk₁.mem]; exact h.hH,
      fun ha => by rw [hk₁.mem]; exact h.abs ha, h.whole, by rw [hk₁.mem]; exact h.frame⟩, by omega⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (x.length + j) % 16 = 0 := h.whole.resolve_left (by omega)
    have hdj := h.data.sub (j := j) (k := 16 * nb) (by omega) (by omega)
    have h9 := he₁.r9; have h10 := he₁.r10; have h11 := he₁.r11
    obtain ⟨s₂, run₂, h0', h1', h12', hg₂, hk₂⟩ : ∃ s₂, runBlock isa
        [addI .r0 .r9 240, addI .r1 .r10 yo, addI .r12 .r11 scrO] s₁ = some s₂ ∧
        s₂.gpr .r0 = c + BitVec.ofNat 32 240 ∧ s₂.gpr .r1 = st + BitVec.ofNat 32 yo ∧
        s₂.gpr .r12 = w + BitVec.ofNat 32 512 ∧
        (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r12 → s₂.gpr r = s₁.gpr r) ∧ VG.Proof.AesGcm.Arm.Keeps s₁ s₂ := by
      refine ⟨_, by arun [show encodable (BitVec.ofNat 32 yo) = true by rcases hyo with rfl | rfl <;> decide], ?_,
        ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h9]
      · simp [gpr_setReg, h10]
      · simp [gpr_setReg, h11]
      · intro r a b d; simp [gpr_setReg, a, b, d]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide)) hk₂.sp hk₂.rd hk₂.wr
    have eD := h.data.addr (j := j) (by omega)
    refine WP.mono (VG.Proof.AesGcm.Arm.ghCall_ok L hyo he₂ (P := D + BitVec.ofNat 32 j) (n := nb) h0' h1'
      (by rw [hg₂ _ (by decide) (by decide) (by decide), h2])
      (by rw [hg₂ _ (by decide) (by decide) (by decide), h3]) h12' (by have := hdj.fit; omega)
      (hdj.st.sub_right (Lay.stSub (by omega))).symm (hdj.w.sub_right (Lay.wSub (by decide))) hdj.stk
      (by rw [hk₂.rd, hk₂.wr, hk₁.rd, hk₁.wr]; exact hdj.rd)) fun s₃ g => ?_
    refine ⟨j + 16 * nb, by omega, ⟨g.env he₂, by omega, ?_, ?_, hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr), ?_, ?_,
      .inr (by omega), ?_⟩, by omega⟩
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide), h4]
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide), h5]
    · rw [VG.Proof.AesGcm.Arm.blockAt_frame g.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact L.ctx_st (by decide) (by omega)
        · exact L.ctx_w (by decide) (by decide)
        · exact (L.stk_ctx (by decide)).symm), hk₂.mem, hk₁.mem]; exact h.hH
    · intro ha
      have ex : x ++ bytesAt m₀ (State.addr D) (j + 16 * nb) =
          (x ++ bytesAt m₀ (State.addr D) j) ++ bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (16 * nb) := by
        rw [VG.Proof.AesGcm.Arm.bytesAt_add, List.append_assoc]
      rw [ex]
      refine Proof.Gcm.absorb_whole (h.abs ha) (by simp [VG.Proof.AesGcm.Arm.length_bytesAt]; omega) (by simp [VG.Proof.AesGcm.Arm.length_bytesAt]) ?_
      rw [g.out, hk₂.mem, hk₁.mem, h.hH, Proof.Gcm.blocksAt_eq, eD]
      congr 2
      -- The data is as in `m₀`.
      have e₁ := congrArg (fun l => l.drop j) hm₀
      have e₂ : ∀ m : Mem, (bytesAt m (State.addr D) n).drop j =
          bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j) := fun m => by
        rw [show n = j + (n - j) by omega, VG.Proof.AesGcm.Arm.bytesAt_add, List.drop_left' (VG.Proof.AesGcm.Arm.length_bytesAt _ _ _),
          Nat.add_sub_cancel_left]
      simp only [e₂] at e₁
      have e₃ := congrArg (fun l => l.take (16 * nb)) e₁
      have e₄ : ∀ m : Mem, (bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j)).take (16 * nb) =
          bytesAt m (State.addr D + BitVec.ofNat 64 j) (16 * nb) := fun m => by
        rw [show n - j = 16 * nb + (n - j - 16 * nb) by omega, VG.Proof.AesGcm.Arm.bytesAt_add,
          List.take_left' (VG.Proof.AesGcm.Arm.length_bytesAt _ _ _)]
      simp only [e₄] at e₃
      exact e₃
    · have := g.frame; rw [hk₂.mem, hk₁.mem] at this; exact h.frame.trans (VG.Proof.AesGcm.Arm.gh_absFrame this)

/-- The last bytes, buffered. -/
theorem tail_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.AbsMid c st w sp k7 k8 yo H x D n m₀ j s) (hj : n - j < 16)
    (hm₀ : bytesAt s.mem (State.addr D) n = bytesAt m₀ (State.addr D) n) :
    WP isa absorbTail s (VG.Proof.AesGcm.Arm.AbsOut c st w sp k7 k8 yo H x (x ++ bytesAt m₀ (State.addr D) n) m₀) := by
  have hn' := h.data.lt32
  have he := h.env
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := VG.Proof.AesGcm.Arm.cmp0_ok s .r5 h.r5 (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s₁ := he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁
  refine WP.ite (decide (n - j = 0)) (VG.Proof.AesGcm.Arm.eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega
    subst h0
    exact WP.block_nil ⟨he₁, fun ha => by rw [hm₁]; exact h.abs ha, by rw [hm₁]; exact h.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    have hw : (x.length + j) % 16 = 0 := h.whole.resolve_left h0
    have hdj := h.data.sub (j := j) (k := n - j) (by omega) (by omega)
    have eD := h.data.addr (j := j) (by omega)
    have h10 := he₁.r10
    obtain ⟨s₂, run₂, h1', h2', h3', hg₂, hk₂⟩ : ∃ s₂, runBlock isa
        [.mov .r1 (.reg .r4), addI .r2 .r10 32, .mov .r3 (.reg .r5)] s₁ = some s₂ ∧
        s₂.gpr .r1 = D + BitVec.ofNat 32 j ∧ s₂.gpr .r2 = st + BitVec.ofNat 32 32 ∧
        s₂.gpr .r3 = BitVec.ofNat 32 (n - j) ∧
        (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ VG.Proof.AesGcm.Arm.Keeps s₁ s₂ := by
      refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, hg₁, h.r4]
      · simp [gpr_setReg, h10]
      · simp [gpr_setReg, hg₁, h.r5]
      · intro r a b d; simp [gpr_setReg, a, b, d]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have eB := L.stA (d := 32) (by decide)
    have lp : VG.Proof.AesGcm.Arm.LoopPre s₂ (D + BitVec.ofNat 32 j) (st + BitVec.ofNat 32 32) (n - j) := by
      refine ⟨h1', h2', h3', by omega, by omega, hdj.fit, by rw [L.stN (by decide)]; have := L.sw; omega, ?_, ?_, ?_⟩
      · rw [hk₂.rd, hk₂.wr, hrd₁, hwr₁]; exact hdj.rd
      · rw [hk₂.wr, hwr₁, eB]; exact he.perm.stC (by omega)
      · rw [eB]; exact hdj.st.sub_right (Lay.stSub (by omega))
    refine WP.mono (VG.Proof.AesGcm.Arm.copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
    rw [hk₂.mem, hm₁, eB, eD] at hm₃
    have hlen := VG.Proof.AesGcm.Arm.length_bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j)
    have fw : Frame [⟨State.addr st + BitVec.ofNat 64 32, n - j⟩] s.mem s₃.mem := by
      rw [hm₃]; exact VG.Proof.AesGcm.Arm.writeBytes_frame' _ hlen
    refine ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hg₂ _ (by decide) (by decide) (by decide)]) (lo.sp.trans hk₂.sp) (lo.rd.trans hk₂.rd)
          (lo.wr.trans hk₂.wr), ?_, ?_⟩
    · intro ha
      have ex : x ++ bytesAt m₀ (State.addr D) n =
          (x ++ bytesAt m₀ (State.addr D) j) ++ bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j) := by
        rw [List.append_assoc, ← VG.Proof.AesGcm.Arm.bytesAt_add, Nat.add_sub_cancel' h.le]
      have ed : bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j) =
          bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j) := by
        have e₁ := congrArg (fun l => l.drop j) hm₀
        have e₂ : ∀ m : Mem, (bytesAt m (State.addr D) n).drop j =
            bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j) := fun m => by
          rw [show n = j + (n - j) by omega, VG.Proof.AesGcm.Arm.bytesAt_add, List.drop_left' (VG.Proof.AesGcm.Arm.length_bytesAt _ _ _),
            Nat.add_sub_cancel_left]
        simpa only [e₂] using e₁
      rw [ex, ← ed]
      refine Proof.Gcm.absorb_tail (h.abs ha) (by simp [VG.Proof.AesGcm.Arm.length_bytesAt]; omega) (by rw [hlen]; omega) ?_ ?_
      · rw [VG.Proof.AesGcm.Arm.blockAt_frame fw fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by omega)) (by omega) (by omega)]
      · rw [hm₃]; exact VG.Proof.AesGcm.Arm.bytesAt_writeBytes_self _ _ _ (by rw [hlen]; omega)
    · exact h.frame.trans ((fw.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by omega)⟩))

omit L hyo in
theorem AbsIn.keep {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s s' : State}
    (h : VG.Proof.AesGcm.Arm.AbsIn c st w sp k7 k8 yo H x D n s) (hg : s'.gpr = s.gpr) (hk : VG.Proof.AesGcm.Arm.Keeps s s') : VG.Proof.AesGcm.Arm.AbsIn c st w sp k7 k8 yo H x D n s' where
  env := h.env.keep (fun r _ => by rw [hg]) hk.sp hk.rd hk.wr
  r4 := by rw [hg]; exact h.r4
  r5 := by rw [hg]; exact h.r5
  r6 := by rw [hg]; exact h.r6
  data := h.data.of_eq hk.rd hk.wr
  hH := by rw [hk.mem]; exact h.hH

omit L in
theorem AbsMid.data_eq {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.AbsMid c st w sp k7 k8 yo H x D n m₀ j s) : bytesAt s.mem (State.addr D) n = bytesAt m₀ (State.addr D) n :=
  VG.Proof.AesGcm.Arm.bytesAt_frame h.frame (VG.Proof.AesGcm.Arm.data_absFrame hyo h.data) (by have := h.data.lt; omega)

/-- After the first test: the buffer filled if it holds bytes. -/
theorem absorbFill_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.AbsIn c st w sp k7 k8 yo H x D n s) (h0 : n ≠ 0) :
    WP isa (absorbFill yo) s (fun s' => ∃ j, j = (if x.length % 16 = 0 then 0 else min (16 - x.length % 16) n) ∧
      VG.Proof.AesGcm.Arm.AbsMid c st w sp k7 k8 yo H x D n s.mem j s') := by
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂, hsp₂⟩ := VG.Proof.AesGcm.Arm.cmp0_ok s .r6 h.r6
    (by have := Nat.mod_lt x.length (show 16 > 0 by decide); omega)
  have h₂ := h.keep hg₂ ⟨hm₂, hrd₂, hwr₂, hsp₂⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.ite (decide (x.length % 16 = 0)) (VG.Proof.AesGcm.Arm.eval_eq' hz₂) (fun ht => ?_) (fun hf => ?_)
  · have ho : x.length % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, by simp [ho], h₂.env, by omega, by rw [h₂.r4, VG.Proof.AesGcm.Arm.add_ofNat_zero], by rw [h₂.r5, Nat.sub_zero], h₂.data,
      h₂.hH, fun ha => by rw [hm₂]; simpa [bytesAt] using ha, .inr (by omega), by rw [hm₂]; exact Frame.refl _ _⟩
  · have ho : x.length % 16 ≠ 0 := by simpa using hf
    have := VG.Proof.AesGcm.Arm.head_ok L hyo h₂ h0 ho
    rw [hm₂] at this
    exact WP.mono this fun _ ⟨j, hj, hm⟩ => ⟨j, by simp only [ho, ite_false]; exact hj, hm⟩

/-- `absorb yo`. -/
theorem absorb_ok {H : Block} {x : List Byte} {D : BitVec 32} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.AbsIn c st w sp k7 k8 yo H x D n s) :
    WP isa (absorb yo) s (VG.Proof.AesGcm.Arm.AbsOut c st w sp k7 k8 yo H x (x ++ bytesAt s.mem (State.addr D) n) s.mem) := by
  have hn' := h.data.lt32
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := VG.Proof.AesGcm.Arm.cmp0_ok s .r5 h.r5 hn'
  have h₁ := h.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (VG.Proof.AesGcm.Arm.eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨h₁.env, fun ha => by rw [hm₁]; simpa [bytesAt] using ha, by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    rw [← hm₁]
    refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.absorbFill_ok L hyo h₁ h0) fun s' ⟨j, _, hj⟩ => ?_)
    refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.whole_ok L hyo hj (hj.data_eq hyo)) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact VG.Proof.AesGcm.Arm.tail_ok L hyo hj' hlt (hj'.data_eq hyo)

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Words`. -/
section

/-!
# AES-GCM on ARMv7: words and the lengths block

Untrusted: everything here is checked by Lean. `rev` is `byteRev32`; the
bytes of a block of two 64-bit values are their big-endian bytes
(`toBytes_append64`); and `8 x` of a 64-bit `x = hi:lo`, as the code computes
it with shifts (`shl3_words`).
-/

namespace VG.Proof.AesGcm.Arm

open VG
open VG.Spec.Gcm (be64 toBytes)

theorem rev_eq : VG.Arm.rev = byteRev32 := rfl

theorem toBytes_append64 (a c : BitVec 64) : toBytes (a ++ c) = be64 a.toNat ++ be64 c.toNat := by
  have ha := a.isLt; have hc := c.isLt
  have e : (a ++ c).toNat = a.toNat * 2 ^ 64 + c.toNat := Proof.Gcm.toNat_append a c
  simp only [toBytes, be64, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, e]
    omega

/-- `8 x`, of `x = hi:lo`, in two words, as `lsl #3` and `orr` with `lsr #29`. -/
theorem shl3_words (hi lo : BitVec 32) :
    (((hi <<< 3) ||| (lo >>> 29)) ++ (lo <<< 3) : BitVec 64) = (hi ++ lo) <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  have h₁ := hi.isLt; have h₂ := lo.isLt
  simp only [Proof.Gcm.toNat_append, BitVec.toNat_shiftLeft, BitVec.toNat_or, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hor : (hi.toNat * 2 ^ 3 % 2 ^ 32) ||| (lo.toNat / 2 ^ 29) = hi.toNat * 2 ^ 3 % 2 ^ 32 + lo.toNat / 2 ^ 29 := by
    have : lo.toNat / 2 ^ 29 < 2 ^ 3 := by omega
    rw [show hi.toNat * 2 ^ 3 % 2 ^ 32 = 2 ^ 3 * (hi.toNat % 2 ^ 29) by omega, Nat.mul_comm,
      ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt this]
  rw [hor]
  omega

/-- `8 x` modulo 2⁶⁴, as a number. -/
theorem shl3_toNat (x : BitVec 64) : (x <<< 3).toNat = 8 * x.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; congr 1; omega

theorem toBytes_append4 (a b c d : BitVec 32) :
    toBytes (a ++ b ++ c ++ d) = be64 (a ++ b).toNat ++ be64 (c ++ d).toNat := by
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  have e : (a ++ b ++ c ++ d).toNat = ((a.toNat * 2 ^ 32 + b.toNat) * 2 ^ 32 + c.toNat) * 2 ^ 32 + d.toNat := by
    simp only [Proof.Gcm.toNat_append]
  have e₁ : (a ++ b).toNat = a.toNat * 2 ^ 32 + b.toNat := Proof.Gcm.toNat_append a b
  have e₂ : (c ++ d).toNat = c.toNat * 2 ^ 32 + d.toNat := Proof.Gcm.toNat_append c d
  simp only [toBytes, be64, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq, and_true, e₁, e₂]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, e]
    omega

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Flush`. -/
section

/-!
# AES-GCM on ARMv7: padding the buffer (`flush`) and the lengths block (`lens`)

Untrusted: everything here is checked by Lean. `flush yo` pads the `r6`
buffered bytes with zeros in `T` and absorbs them (`flush_ok`); `lens yo`
stores the lengths block of `r5:r4` and `r7:r6` bytes in `T` and absorbs it
(`lens_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ghash blocks zeros padLen)
open VG.Proof.Gcm (Absorbed lensBlock)
open VG.Proof.Cmac (le4 store4)

/-- The regions `flush` and `lens` write. -/
abbrev tFrame (st w sp : BitVec 32) (yo : Nat) : List Region :=
  [⟨State.addr st + BitVec.ofNat 64 yo, 16⟩, ⟨State.addr w + BitVec.ofNat 64 96, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, VG.Proof.AesGcm.Arm.below sp]

theorem gh_tFrame {st w sp : BitVec 32} {yo : Nat} {m m' : Mem}
    (h : Frame [⟨State.addr st + BitVec.ofNat 64 yo, 16⟩, ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, VG.Proof.AesGcm.Arm.below sp] m m') :
    Frame (VG.Proof.AesGcm.Arm.tFrame st w sp yo) m m' :=
  h.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

theorem store4_zero_bytes (m : Mem) (p : Addr) : bytesAt (store4 m p 0 0 0 0) p 16 = zeros 16 := by
  rw [Cmac.bytesAt_store4, Cmac.le4_zero]; rfl

/-- The four words at `p`, as the code stores them at `b + o`, `b + o + 4`, … -/
theorem store4_eq (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ : BitVec 32) :
    store4 m p w₀ w₁ w₂ w₃ = (((m.writeW p w₀).writeW (p + BitVec.ofNat 64 4) w₁).writeW (p + BitVec.ofNat 64 8)
      w₂).writeW (p + BitVec.ofNat 64 12) w₃ := rfl

/-- Before `flush yo` (or `lens yo`): GHASH has absorbed `x`. -/
structure FlIn (c st w sp k7 k8 : BitVec 32) (H : Block) (s : State) : Prop where
  env : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H

/-- After `flush yo`: GHASH has absorbed `x`, from `m₀`. -/
structure FlOut (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (x₀ x : List Byte) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  abs : Absorbed m₀ (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x₀ →
    Absorbed s.mem (State.addr st + BitVec.ofNat 64 yo) (State.addr st + BitVec.ofNat 64 32) H x
  frame : Frame (VG.Proof.AesGcm.Arm.tFrame st w sp yo) m₀ s.mem

/-- After the copy of the buffered bytes to `T`, padded with zeros. -/
structure FlMid (c st w sp k7 k8 : BitVec 32) (yo : Nat) (H : Block) (o : Nat) (m₀ : Mem) (s : State) : Prop where
  env : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s
  hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H
  hT : bytesAt s.mem (State.addr w + BitVec.ofNat 64 96) 16 =
    bytesAt m₀ (State.addr st + BitVec.ofNat 64 32) o ++ zeros (16 - o)
  hY : blockAt s.mem (State.addr st + BitVec.ofNat 64 yo) = blockAt m₀ (State.addr st + BitVec.ofNat 64 yo)
  frame : Frame [⟨State.addr w + BitVec.ofNat 64 96, 16⟩] m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

theorem ctx_tFrame : ∀ r ∈ VG.Proof.AesGcm.Arm.tFrame st w sp yo, (⟨State.addr c + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_w (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

/-- The `o` buffered bytes copied to `T`, padded with zeros. -/
theorem flushCopy_ok {H : Block} {o : Nat} {s : State} (h : VG.Proof.AesGcm.Arm.FlIn c st w sp k7 k8 H s)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 o) (ho : o < 16) (h0 : o ≠ 0) :
    WP isa (.seq (.block flushPre) copyLoop) s (VG.Proof.AesGcm.Arm.FlMid c st w sp k7 k8 yo H o s.mem) := by
  have he := h.env
  have h10 := he.r10; have h11 := he.r11
  have w₀ := he.perm.wW (show 96 + 4 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 100 + 4 ≤ 2560 by decide)
  have w₂ := he.perm.wW (show 104 + 4 ≤ 2560 by decide)
  have w₃ := he.perm.wW (show 108 + 4 ≤ 2560 by decide)
  obtain ⟨s₂, run₂, hm₂, h1, h2, h3, hg₂, hk₂⟩ : ∃ s₂, runBlock isa flushPre s = some s₂ ∧
      s₂.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 96) 0 0 0 0 ∧
      s₂.gpr .r1 = st + BitVec.ofNat 32 32 ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 96 ∧
      s₂.gpr .r3 = BitVec.ofNat 32 o ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.sp = s.sp := by
    refine ⟨_, by simp only [flushPre]; arun [h10, h11, L.wA, L.stA, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, VG.Proof.AesGcm.Arm.store4_eq, VG.Proof.AesGcm.Arm.add_ofNat_assoc]; rfl
    · simp [gpr_setReg, h10]
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, h6]
    · intro r a b d e; simp [gpr_setReg, a, b, d, e]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have eS := L.stA (d := 32) (by decide)
  have eT := L.wA (d := 96) (by decide)
  have lp : VG.Proof.AesGcm.Arm.LoopPre s₂ (st + BitVec.ofNat 32 32) (w + BitVec.ofNat 32 96) o := by
    refine ⟨h1, h2, h3, by omega, by omega, by rw [L.stN (by decide)]; have := L.sw; omega,
      by rw [L.wN (by decide)]; have := L.ww; omega, ?_, ?_, ?_⟩
    · rw [hk₂.1, hk₂.2.1, eS]; exact VG.Proof.AesGcm.Arm.covers_left (he.perm.stC (by omega))
    · rw [hk₂.2.1, eT]; exact he.perm.wC (by omega)
    · rw [eS, eT]; exact L.st_w (by omega) (.inr ⟨by decide, by omega⟩)
  refine WP.mono (VG.Proof.AesGcm.Arm.copyLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [eS, eT] at hm₃
  -- The memory so far.
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by rw [hm₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hB₂ : bytesAt s₂.mem (State.addr st + BitVec.ofNat 64 32) o = bytesAt s.mem (State.addr st + BitVec.ofNat 64 32) o :=
    VG.Proof.AesGcm.Arm.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩))
      (by omega)
  have hlen := VG.Proof.AesGcm.Arm.length_bytesAt s₂.mem (State.addr st + BitVec.ofNat 64 32) o
  have fc : Frame [⟨State.addr w + BitVec.ofNat 64 96, o⟩] s₂.mem s₃.mem := by
    rw [hm₃]; exact VG.Proof.AesGcm.Arm.writeBytes_frame' _ hlen
  have f₃ : Frame [⟨State.addr w + BitVec.ofNat 64 96, 16⟩] s.mem s₃.mem :=
    fz.trans (fc.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
          hg₂ _ (by decide) (by decide) (by decide) (by decide)])
      (lo.sp.trans hk₂.2.2) (lo.rd.trans hk₂.1) (lo.wr.trans hk₂.2.1), ?_, ?_, ?_, f₃⟩
  · rw [VG.Proof.AesGcm.Arm.blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), h.hH]
  · rw [hm₃, VG.Proof.AesGcm.Arm.bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega) (by decide), hlen, hB₂]
    congr 1
    have := VG.Proof.AesGcm.Arm.store4_zero_bytes s.mem (State.addr w + BitVec.ofNat 64 96)
    rw [← hm₂, show (16 : Nat) = o + (16 - o) by omega, VG.Proof.AesGcm.Arm.bytesAt_add] at this
    have e := congrArg (List.drop o) this
    rw [List.drop_left' (VG.Proof.AesGcm.Arm.length_bytesAt _ _ _)] at e
    rw [e, show o + (16 - o) = 16 by omega, Spec.Gcm.zeros, List.drop_replicate]
    rfl
  · exact VG.Proof.AesGcm.Arm.blockAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)

/-- The padded buffer absorbed. -/
theorem flushGh_ok {H : Block} {x : List Byte} {m₀ : Mem} {s : State}
    (h : VG.Proof.AesGcm.Arm.FlMid c st w sp k7 k8 yo H (x.length % 16) m₀ s) (h0 : x.length % 16 ≠ 0) :
    WP isa (ghash1 yo .r11 tO) s (VG.Proof.AesGcm.Arm.FlOut c st w sp k7 k8 yo H x (x ++ zeros (padLen x.length)) m₀) := by
  have he := h.env
  have eT := L.wA (d := 96) (by decide)
  refine WP.mono (VG.Proof.AesGcm.Arm.ghash1_ok L hyo he .r11 96 (.inr rfl) (by decide) (P := w + BitVec.ofNat 32 96)
    (by rw [he.r11]) (by rw [L.wN (by decide)]; have := L.ww; omega) ?_ ?_ ?_ ?_) fun s₄ g => ?_
  · rw [eT]; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · rw [eT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [eT]; exact L.stk_w (by decide)
  · rw [eT]; exact VG.Proof.AesGcm.Arm.covers_left (he.perm.wC (by decide))
  refine ⟨g.env he, ?_, ?_, ?_⟩
  · rw [VG.Proof.AesGcm.Arm.blockAt_frame g.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.ctx_st (by decide) (by omega)
      · exact L.ctx_w (by decide) (by decide)
      · exact (L.stk_ctx (by decide)).symm), h.hH]
  · intro ha
    refine Proof.Gcm.absorb_pad ha h0 (B := bytesAt s.mem (State.addr w + BitVec.ofNat 64 96) 16) h.hT ?_
    rw [g.out, h.hY, h.hH, eT]; rfl
  · refine (h.frame.sub fun r hr => ?_).trans (VG.Proof.AesGcm.Arm.gh_tFrame g.frame)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

/-- `flush yo`. -/
theorem flush_ok {H : Block} {x : List Byte} {s : State} (h : VG.Proof.AesGcm.Arm.FlIn c st w sp k7 k8 H s)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 (x.length % 16)) :
    WP isa (flush yo) s (VG.Proof.AesGcm.Arm.FlOut c st w sp k7 k8 yo H x (x ++ zeros (padLen x.length)) s.mem) := by
  have he := h.env
  have hlt := Nat.mod_lt x.length (show 16 > 0 by decide)
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := VG.Proof.AesGcm.Arm.cmp0_ok s .r6 h6 (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s₁ := he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁
  refine WP.ite (decide (x.length % 16 = 0)) (VG.Proof.AesGcm.Arm.eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : x.length % 16 = 0 := by simpa using ht
    rw [Proof.Gcm.padLen_of_mod h0]
    exact WP.block_nil ⟨he₁, by rw [hm₁]; exact h.hH, fun ha => by rw [hm₁]; simpa [zeros] using ha,
      by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : x.length % 16 ≠ 0 := by simpa using hf
    rw [← hm₁]
    refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.flushCopy_ok L hyo (o := x.length % 16) ⟨he₁, by rw [hm₁]; exact h.hH⟩
      (by rw [hg₁]; exact h6) hlt h0) fun s₃ hm => VG.Proof.AesGcm.Arm.flushGh_ok L hyo hm h0)

end

/-- `[8 (hi:lo)]₆₄` into `W + o`, as two byte-reversed words. -/
theorem be64Store_ok {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp) {s : State} (he : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s)
    (lo hi : Reg) (hlo : lo ≠ .r0) (o : Nat) (ho : o + 8 ≤ 2560) :
    ∃ s', runBlock isa (be64Store lo hi o) s = some s' ∧
      s'.mem = (s.mem.writeW (State.addr w + BitVec.ofNat 64 o) (byteRev32 ((s.gpr hi <<< 3) ||| (s.gpr lo >>> 29)))).writeW
        (State.addr w + BitVec.ofNat 64 o + BitVec.ofNat 64 4) (byteRev32 (s.gpr lo <<< 3)) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have w₀ := he.perm.wW (show o + 4 ≤ 2560 by omega)
  have w₁ := he.perm.wW (show o + 4 + 4 ≤ 2560 by omega)
  have e₁ := L.wA (d := o) (by omega)
  have e₂ := L.wA (d := o + 4) (by omega)
  have o₁ : o < 4096 := by omega
  have o₂ : o + 4 < 4096 := by omega
  refine ⟨_, by simp only [be64Store]; arun [h11, e₁, e₂, w₀, w₁, hlo, o₁, o₂], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, VG.Proof.AesGcm.Arm.mem_store, gpr_setReg, ite_true, ite_false, hlo, VG.Proof.AesGcm.Arm.add_ofNat_assoc, VG.Proof.AesGcm.Arm.rev_eq]
  · intro r a; simp [gpr_setReg, a]
  all_goals rfl

/-- `[8 (r5:r4)]₆₄ ‖ [8 (r7:r6)]₆₄`, the lengths block, stored in `T`. -/
theorem lensStore_ok {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp) {s : State} (he : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s) :
    WP isa (.block (be64Store .r4 .r5 tO ++ be64Store .r6 .r7 (tO + 8))) s fun s' =>
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 96)
        (byteRev32 ((s.gpr .r5 <<< 3) ||| (s.gpr .r4 >>> 29))) (byteRev32 (s.gpr .r4 <<< 3))
        (byteRev32 ((s.gpr .r7 <<< 3) ||| (s.gpr .r6 >>> 29))) (byteRev32 (s.gpr .r6 <<< 3)) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, run₁, hm₁, hg₁, hrd₁, hwr₁, hsp₁⟩ := VG.Proof.AesGcm.Arm.be64Store_ok L he .r4 .r5 (by decide) tO (by decide)
  have he₁ : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)) hsp₁ hrd₁ hwr₁
  obtain ⟨s₂, run₂, hm₂, hg₂, hrd₂, hwr₂, hsp₂⟩ := VG.Proof.AesGcm.Arm.be64Store_ok L he₁ .r6 .r7 (by decide) (tO + 8)
    (by decide)
  refine WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩)
  refine ⟨?_, fun r hr => by rw [hg₂ r hr, hg₁ r hr], hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁⟩
  rw [hm₂, hm₁, hg₁ .r6 (by decide), hg₁ .r7 (by decide)]
  simp only [VG.Proof.AesGcm.Arm.store4_eq, tO, VG.Proof.AesGcm.Arm.add_ofNat_assoc]

theorem lensBlock_eq (a₀ a₁ c₀ c₁ : BitVec 32) :
    le4 (byteRev32 ((a₁ <<< 3) ||| (a₀ >>> 29))) ++ le4 (byteRev32 (a₀ <<< 3)) ++
        le4 (byteRev32 ((c₁ <<< 3) ||| (c₀ >>> 29))) ++ le4 (byteRev32 (c₀ <<< 3)) =
      lensBlock (a₁ ++ a₀).toNat (c₁ ++ c₀).toNat := by
  rw [Cmac.le4_rev4, VG.Proof.AesGcm.Arm.toBytes_append4, VG.Proof.AesGcm.Arm.shl3_words, VG.Proof.AesGcm.Arm.shl3_words, VG.Proof.AesGcm.Arm.shl3_toNat, VG.Proof.AesGcm.Arm.shl3_toNat, Proof.Gcm.be64_mod,
    Proof.Gcm.be64_mod]
  rfl

section
variable {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

/-- The lengths block of `r5:r4` and `r7:r6` bytes, absorbed. -/
theorem lens_ok {H : Block} {s : State} (he : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s)
    (hH : blockAt s.mem (State.addr c + BitVec.ofNat 64 240) = H) :
    WP isa (lens yo) s fun s' => VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s' ∧
      blockAt s'.mem (State.addr c + BitVec.ofNat 64 240) = H ∧
      blockAt s'.mem (State.addr st + BitVec.ofNat 64 yo) = ghashFrom H (blockAt s.mem (State.addr st + BitVec.ofNat 64 yo))
        [Spec.Gcm.ofBytes (lensBlock (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat)] ∧
      Frame (VG.Proof.AesGcm.Arm.tFrame st w sp yo) s.mem s'.mem := by
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.lensStore_ok L he) fun s₂ ⟨hm₂, hg₂, hrd₂, hwr₂, hsp₂⟩ => ?_)
  have he₂ : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide)) hsp₂ hrd₂ hwr₂
  have fT : Frame [⟨State.addr w + BitVec.ofNat 64 96, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hT : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 96) 16 =
      lensBlock (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat := by
    rw [hm₂, Cmac.bytesAt_store4, VG.Proof.AesGcm.Arm.lensBlock_eq]
  have hY₂ : blockAt s₂.mem (State.addr st + BitVec.ofNat 64 yo) = blockAt s.mem (State.addr st + BitVec.ofNat 64 yo) :=
    VG.Proof.AesGcm.Arm.blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  have hH₂ : blockAt s₂.mem (State.addr c + BitVec.ofNat 64 240) = H := by
    rw [VG.Proof.AesGcm.Arm.blockAt_frame fT fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.ctx_w (by decide) (by decide), hH]
  have eT := L.wA (d := 96) (by decide)
  refine WP.mono (VG.Proof.AesGcm.Arm.ghash1_ok L hyo he₂ .r11 96 (.inr rfl) (by decide) (P := w + BitVec.ofNat 32 96)
    (by rw [he₂.r11]) (by rw [L.wN (by decide)]; have := L.ww; omega) ?_ ?_ ?_ ?_) fun s₃ g => ?_
  · rw [eT]; exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · rw [eT]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [eT]; exact L.stk_w (by decide)
  · rw [eT]; exact VG.Proof.AesGcm.Arm.covers_left (he₂.perm.wC (by decide))
  refine ⟨g.env he₂, ?_, ?_, ?_⟩
  · rw [VG.Proof.AesGcm.Arm.blockAt_frame g.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.ctx_st (by decide) (by omega)
      · exact L.ctx_w (by decide) (by decide)
      · exact (L.stk_ctx (by decide)).symm), hH₂]
  · have hb : blockAt s₂.mem (State.addr w + BitVec.ofNat 64 96) =
        Spec.Gcm.ofBytes (lensBlock (s.gpr .r5 ++ s.gpr .r4).toNat (s.gpr .r7 ++ s.gpr .r6).toNat) := by
      rw [blockAt, hT]
    rw [g.out, hY₂, hH₂, eT, hb]
  · refine (fT.sub fun r hr => ?_).trans (VG.Proof.AesGcm.Arm.gh_tFrame g.frame)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

end

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.Crypt`. -/
section

/-!
# AES-GCM on ARMv7: counter mode over a piece (`crypt`)

Untrusted: everything here is checked by Lean. `crypt` XORs the keystream,
from byte `P` of the text on, into the `r5` bytes at `r4`, where `r6` is
`P mod 16` and the state holds the counter block and the keystream block for
`P` bytes (`Proof.Gcm.Ctr`): the rest of the keystream block (`cryptHead`),
whole blocks with `vg_aes_ctr32` (`cryptWhole`), then a new keystream block
for the last bytes (`cryptTail`). The number of rounds is in `r8`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- A buffer of `n` bytes at `D` that the code may read and write, apart from
the context, the state, `W` and the stack below `sp`. -/
structure DataW (c st w sp k7 k8 : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  ok : VG.Proof.AesGcm.Arm.DataOk st w sp s D n
  wr : Covers [⟨State.addr D, n⟩] s.wr
  ctx : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr D, n⟩

theorem DataW.of_eq {c st w sp k7 k8 : BitVec 32} {s s' : State} {D : BitVec 32} {n : Nat}
    (h : VG.Proof.AesGcm.Arm.DataW c st w sp k7 k8 s D n) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.AesGcm.Arm.DataW c st w sp k7 k8 s' D n :=
  ⟨h.ok.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.ctx⟩

theorem DataW.sub {c st w sp k7 k8 : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesGcm.Arm.DataW c st w sp k7 k8 s D n)
    {j k : Nat} (hjk : j + k ≤ n) (hk : 0 < k) : VG.Proof.AesGcm.Arm.DataW c st w sp k7 k8 s (D + BitVec.ofNat 32 j) k := by
  have ha := h.ok.addr (j := j) (by omega)
  have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 j, k⟩ ⟨State.addr D, n⟩ := Offset.sub_base _ hjk
  exact ⟨h.ok.sub hjk hk, by rw [ha]; exact VG.Proof.AesGcm.Arm.covers_off h.wr hjk h.ok.lt, by rw [ha]; exact h.ctx.sub_right hs⟩

theorem DataW.take {c st w sp k7 k8 : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : VG.Proof.AesGcm.Arm.DataW c st w sp k7 k8 s D n)
    {k : Nat} (hk : k ≤ n) : VG.Proof.AesGcm.Arm.DataW c st w sp k7 k8 s D k :=
  ⟨h.ok.take hk, VG.Proof.AesGcm.Arm.covers_prefix h.wr hk, h.ctx.sub_right (Region.sub_prefix hk)⟩

/-- The cipher of the key schedule in the context, for `R` rounds. -/
abbrev ciphOf (m : Mem) (C : Addr) (R : Nat) : Block → Block :=
  aesWith R (bytesAt m C (16 * (R + 1)))

/-- The regions `crypt` writes. -/
abbrev crFrame (st w sp D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr D, n⟩, ⟨State.addr st + BitVec.ofNat 64 48, 32⟩, ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩,
    VG.Proof.AesGcm.Arm.below sp]

/-- Before `crypt`: `P` bytes of text so far, `n` bytes at `D` to go, `R`
rounds in `r8`. -/
structure CrIn (c st w sp k7 k8 : BitVec 32) (R : Nat) (icb : Block) (P : Nat) (D : BitVec 32) (n : Nat) (s : State) :
    Prop where
  env : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s
  r4 : s.gpr .r4 = D
  r5 : s.gpr .r5 = BitVec.ofNat 32 n
  r6 : s.gpr .r6 = BitVec.ofNat 32 (P % 16)
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  data : VG.Proof.AesGcm.Arm.DataW c st w sp k7 k8 s D n

/-- Part of the way: `j` bytes done, from `m₀`. -/
structure CrMid (c st w sp k7 k8 : BitVec 32) (R : Nat) (icb : Block) (P : Nat) (D : BitVec 32) (n : Nat) (m₀ : Mem)
    (j : Nat) (s : State) : Prop where
  env : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s
  le : j ≤ n
  r4 : s.gpr .r4 = D + BitVec.ofNat 32 j
  r5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  data : VG.Proof.AesGcm.Arm.DataW c st w sp k7 k8 s D n
  ctr : Ctr m₀ (State.addr st + BitVec.ofNat 64 48) (State.addr st + BitVec.ofNat 64 64) (VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R)
      icb P →
    Ctr s.mem (State.addr st + BitVec.ofNat 64 48) (State.addr st + BitVec.ofNat 64 64) (VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R)
      icb (P + j)
  done : Ctr m₀ (State.addr st + BitVec.ofNat 64 48) (State.addr st + BitVec.ofNat 64 64)
      (VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R) icb P →
    bytesAt s.mem (State.addr D) j = xorKs (VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R) icb P (bytesAt m₀ (State.addr D) j)
  rest : bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (VG.Proof.AesGcm.Arm.crFrame st w sp D n) m₀ s.mem

/-- After `crypt`. -/
structure CrOut (c st w sp k7 k8 : BitVec 32) (R : Nat) (icb : Block) (P : Nat) (D : BitVec 32) (n : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  ctr : Ctr m₀ (State.addr st + BitVec.ofNat 64 48) (State.addr st + BitVec.ofNat 64 64) (VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R)
      icb P →
    Ctr s.mem (State.addr st + BitVec.ofNat 64 48) (State.addr st + BitVec.ofNat 64 64) (VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R)
      icb (P + n)
  out : Ctr m₀ (State.addr st + BitVec.ofNat 64 48) (State.addr st + BitVec.ofNat 64 64)
      (VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R) icb P →
    bytesAt s.mem (State.addr D) n = xorKs (VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R) icb P (bytesAt m₀ (State.addr D) n)
  frame : Frame (VG.Proof.AesGcm.Arm.crFrame st w sp D n) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp)
include L

theorem ctx_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : VG.Proof.AesGcm.Arm.DataW c st w sp k7 k8 s D n) :
    ∀ r ∈ VG.Proof.AesGcm.Arm.crFrame st w sp D n, (⟨State.addr c, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

omit L in
theorem ciph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr c, 256⟩ : Region).Disjoint r) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    VG.Proof.AesGcm.Arm.ciphOf m' (State.addr c) R = VG.Proof.AesGcm.Arm.ciphOf m (State.addr c) R := by
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  simp only [VG.Proof.AesGcm.Arm.ciphOf]
  rw [VG.Proof.AesGcm.Arm.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]

end

/-- `[D, D + j)` and `[D + j, D + n)` are apart. -/
theorem split_disj {D : Addr} {j n : Nat} (hj : j ≤ n) (hn : n < 2 ^ 64) :
    (⟨D, j⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 j, n - j⟩ := by
  have := Offset.disjoint D (d := 0) (n := j) (e := j) (k := n - j) (.inl (by omega)) (by omega) (by omega)
  simpa using this

/-- The bytes done so far and the next ones. -/
theorem done_append {m m₀ : Mem} {ciph : Block → Block} {icb : Block} {P : Nat} {D : Addr} {j l : Nat}
    (h₁ : bytesAt m D j = xorKs ciph icb P (bytesAt m₀ D j))
    (h₂ : bytesAt m (D + BitVec.ofNat 64 j) l = xorKs ciph icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) l)) :
    bytesAt m D (j + l) = xorKs ciph icb P (bytesAt m₀ D (j + l)) := by
  rw [VG.Proof.AesGcm.Arm.bytesAt_add, VG.Proof.AesGcm.Arm.bytesAt_add, Proof.Gcm.xorKs_append, h₁, h₂, VG.Proof.AesGcm.Arm.length_bytesAt]

theorem ctr32_single (ciph : Block → Block) (icb x : Block) : Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

end VG.Proof.AesGcm.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesGcm.Arm.CryptOk`. -/
section

/-!
# AES-GCM on ARMv7: `crypt`

Untrusted: everything here is checked by Lean (see `Crypt.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

section
variable {c st w sp k7 k8 : BitVec 32} (L : VG.Proof.AesGcm.Arm.Lay c st w sp)
include L

/-- The rest of the keystream block. -/
theorem cryptHead_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.CrIn c st w sp k7 k8 R icb P D n s) (hn : n ≠ 0) (hP : P % 16 ≠ 0) :
    WP isa cryptHead s (fun s' => ∃ j, j = min (16 - P % 16) n ∧ VG.Proof.AesGcm.Arm.CrMid c st w sp k7 k8 R icb P D n s.mem j s') := by
  have hlt : P % 16 < 16 := Nat.mod_lt _ (by decide)
  have hn' := h.data.ok.lt32
  have he := h.env
  refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.minLen_ok s h.r6 h.r5 (by omega) hn') fun s₁ ⟨h3, hg, hk⟩ => ?_)
  obtain ⟨k, hk'⟩ : ∃ k, min (16 - P % 16) n = k := ⟨_, rfl⟩
  rw [hk'] at h3
  have hk1 : 1 ≤ k := by omega
  have hk16 : P % 16 + k ≤ 16 := by omega
  have hkn : k ≤ n := by omega
  obtain ⟨s₂, run₂, h1, h2, h4, h5, h3', hg₂, hk₂⟩ : ∃ s₂, runBlock isa [addI .r1 .r10 64,
      .dp .add .r1 .r1 (.reg .r6), .mov .r2 (.reg .r4), .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)]
      s₁ = some s₂ ∧
      s₂.gpr .r1 = st + BitVec.ofNat 32 (64 + P % 16) ∧ s₂.gpr .r2 = D ∧
      s₂.gpr .r4 = D + BitVec.ofNat 32 k ∧ s₂.gpr .r5 = BitVec.ofNat 32 (n - k) ∧
      s₂.gpr .r3 = BitVec.ofNat 32 k ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r4 → r ≠ .r5 → s₂.gpr r = s₁.gpr r) ∧ VG.Proof.AesGcm.Arm.Keeps s₁ s₂ := by
    have e10 := hg .r10 (by decide) (by decide)
    have e4 := hg .r4 (by decide) (by decide)
    have e5 := hg .r5 (by decide) (by decide)
    have e6 := hg .r6 (by decide) (by decide)
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e10, e6, he.r10, h.r6, VG.Proof.AesGcm.Arm.add32_ofNat_assoc]
    · simp [gpr_setReg, e4, h.r4]
    · simp [gpr_setReg, e4, h.r4, h3]
    · simp [gpr_setReg, e5, h.r5, h3, VG.Proof.AesGcm.Arm.ofNat_sub32 hkn hn']
    · simp [gpr_setReg, h3]
    · intro r a b c d; simp [gpr_setReg, a, b, c, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hk₂' := hk.trans hk₂
  have eK : State.addr (st + BitVec.ofNat 32 (64 + P % 16)) = State.addr st + BitVec.ofNat 64 (64 + P % 16) :=
    L.stA (by omega)
  have lp : VG.Proof.AesGcm.Arm.LoopPre s₂ (st + BitVec.ofNat 32 (64 + P % 16)) D k := by
    refine ⟨h1, h2, h3', hk1, by omega, by rw [L.stN (by omega)]; have := L.sw; omega,
      by have := h.data.ok.fit; omega, ?_, ?_, ?_⟩
    · rw [hk₂'.rd, hk₂'.wr, eK]; exact VG.Proof.AesGcm.Arm.covers_left (he.perm.stC (by omega))
    · rw [hk₂'.wr]; exact (h.data.take hkn).wr
    · rw [eK]; exact ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by omega))).symm
  refine WP.mono (VG.Proof.AesGcm.Arm.xorLoop_ok s₂ lp) fun s₃ ⟨hm₃, lo⟩ => ?_
  rw [eK, hk₂'.mem] at hm₃
  have hxl := VG.Proof.AesGcm.Arm.length_xorBytes s.mem (State.addr D) (State.addr st + BitVec.ofNat 64 (64 + P % 16)) k
  have fw : Frame [⟨State.addr D, k⟩] s.mem s₃.mem := by rw [hm₃]; exact VG.Proof.AesGcm.Arm.writeBytes_frame' _ hxl
  have hdisjst : ∀ r ∈ [(⟨State.addr D, k⟩ : Region)],
      (⟨State.addr st + BitVec.ofNat 64 48, 16⟩ : Region).Disjoint r ∧
      (⟨State.addr st + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm,
      ((h.data.take hkn).ok.st.sub_right (Lay.stSub (by decide))).symm⟩
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .r4 → r ≠ .r5 → s₃.gpr r = s.gpr r :=
    fun r a b c d e f i => by rw [lo.other r a b c d e, hg₂ r b c f i, hg r d e]
  have he₃ : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s₃ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lo.sp.trans hk₂'.sp) (lo.rd.trans hk₂'.rd) (lo.wr.trans hk₂'.wr)
  have hc₃ : VG.Proof.AesGcm.Arm.ciphOf s₃.mem (State.addr c) R = VG.Proof.AesGcm.Arm.ciphOf s.mem (State.addr c) R :=
    VG.Proof.AesGcm.Arm.ciph_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.data.take hkn).ctx) h.rounds
  refine ⟨k, hk'.symm, he₃, hkn, by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h4],
    by rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h5],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8],
    h.rounds, h.data.of_eq (lo.rd.trans hk₂'.rd) (lo.wr.trans hk₂'.wr), ?_, ?_, ?_, ?_, ?_⟩
  · intro hc₀
    refine (hc₀.head hP hk16).congr (VG.Proof.AesGcm.Arm.blockAt_frame fw fun r hr => (hdisjst r hr).1)
      (VG.Proof.AesGcm.Arm.blockAt_frame fw fun r hr => (hdisjst r hr).2)
  · intro hc₀
    have e := VG.Proof.AesGcm.Arm.bytesAt_writeBytes_self s.mem (State.addr D)
      (VG.Proof.AesGcm.Arm.xorBytes s.mem (State.addr D) (State.addr st + BitVec.ofNat 64 (64 + P % 16)) k) (by rw [hxl]; omega)
    rw [hxl] at e
    rw [hm₃, e, VG.Proof.AesGcm.Arm.xorBytes]
    have := Proof.Gcm.ctr_head hc₀ hP (d := bytesAt s.mem (State.addr D) k) (by rw [VG.Proof.AesGcm.Arm.length_bytesAt]; exact hk16)
    rw [VG.Proof.AesGcm.Arm.length_bytesAt, VG.Proof.AesGcm.Arm.add_ofNat_assoc] at this
    exact this
  · exact VG.Proof.AesGcm.Arm.bytesAt_frame fw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (VG.Proof.AesGcm.Arm.split_disj hkn h.data.ok.lt).symm) (by omega)
  · by_cases hkk : k = n
    · left; omega
    · right; omega
  · exact fw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Region.sub_prefix hkn⟩

omit L in
theorem CrMid.data_eq {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.CrMid c st w sp k7 k8 R icb P D n m₀ j s) : bytesAt s.mem (State.addr D) n =
      bytesAt s.mem (State.addr D) j ++ bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j) := by
  rw [← VG.Proof.AesGcm.Arm.bytesAt_add, Nat.add_sub_cancel' h.le]

omit L in
/-- The split of the rest into whole blocks for `vg_aes_ctr32` and the last bytes. -/
theorem splitCtr_ok {s : State} {D : BitVec 32} {n j : Nat} (hj : j ≤ n) (hn : n < 2 ^ 32)
    (h4 : s.gpr .r4 = D + BitVec.ofNat 32 j) (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)) :
    ∃ s', runBlock isa splitCtr s = some s' ∧
      s'.gpr .r3 = D + BitVec.ofNat 32 j ∧ s'.gpr .r12 = BitVec.ofNat 32 ((n - j) / 16) ∧
      s'.gpr .r4 = D + BitVec.ofNat 32 (j + 16 * ((n - j) / 16)) ∧
      s'.gpr .r5 = BitVec.ofNat 32 (n - (j + 16 * ((n - j) / 16))) ∧
      s'.z = decide ((n - j) / 16 = 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ VG.Proof.AesGcm.Arm.Keeps s s' := by
  have hand := VG.Proof.AesGcm.Arm.and15 (BitVec.ofNat 32 (n - j))
  rw [VG.Proof.AesGcm.Arm.toNat32 (by omega)] at hand
  have hsub : BitVec.ofNat 32 (n - j) - BitVec.ofNat 32 ((n - j) % 16) = BitVec.ofNat 32 (16 * ((n - j) / 16)) := by
    rw [VG.Proof.AesGcm.Arm.ofNat_sub32 (Nat.mod_le _ _) (by omega)]; congr 1; omega
  refine ⟨_, by simp only [splitCtr]; arun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h4]
  · simp [gpr_setReg, h5, VG.Proof.AesGcm.Arm.shr4 (show n - j < 2 ^ 32 by omega)]
  · simp only [gpr_setReg, VG.Proof.AesGcm.Arm.gpr_subFlags, ite_true, ite_false, reduceCtorEq, h4, h5, hand, hsub, VG.Proof.AesGcm.Arm.add32_ofNat_assoc]
  · simp only [gpr_setReg, VG.Proof.AesGcm.Arm.gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, hand]
    congr 1; omega
  · simp only [VG.Proof.AesGcm.Arm.z_subFlags, gpr_setReg, VG.Proof.AesGcm.Arm.gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5,
      VG.Proof.AesGcm.Arm.shr4 (show n - j < 2 ^ 32 by omega)]
    rw [VG.Proof.AesGcm.Arm.z_cmp (by omega) (by decide)]
  · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
  · exact ⟨rfl, rfl, rfl, rfl⟩

omit L in
/-- The arguments of `vg_aes_ctr32` for the whole blocks. -/
theorem wholeArgs_ok {s : State} (he : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa [.mov .r0 (.reg .r9), .mov .r1 (.reg .r8), addI .r2 .r10 48, addI .lr .r11 scrO] s = some s' ∧
      s'.gpr .r0 = c ∧ s'.gpr .r1 = s.gpr .r8 ∧ s'.gpr .r2 = st + BitVec.ofNat 32 48 ∧
      s'.gpr .lr = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ VG.Proof.AesGcm.Arm.Keeps s s' := by
  have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg, h11]
  · intro r a b d e; simp [gpr_setReg, a, b, d, e]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The arguments of `vg_aes_ctr32` on `nb` whole blocks at `D + j`. -/
theorem ctrWhole_mk {R : Nat} {D : BitVec 32} {j nb : Nat} {s : State} (he : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s)
    (h0 : s.gpr .r0 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = st + BitVec.ofNat 32 48)
    (h3 : s.gpr .r3 = D + BitVec.ofNat 32 j) (h12 : s.gpr .r12 = BitVec.ofNat 32 nb)
    (hlr : s.gpr .lr = w + BitVec.ofNat 32 512) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hdj : VG.Proof.AesGcm.Arm.DataW c st w sp k7 k8 s (D + BitVec.ofNat 32 j) (16 * nb)) :
    VG.Proof.AesGcm.Arm.CtrCall s c (st + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) (w + BitVec.ofNat 32 512) R nb := by
  have eC := L.stA (d := 48) (by decide)
  have eS := L.wA (d := 512) (by decide)
  have hk := he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR,
    by rw [hk]; exact L.sp8, by have := L.cw; omega, by rw [L.stN (by decide)]; have := L.sw; omega,
    by have := hdj.ok.fit; omega, by rw [L.wN (by decide)]; have := L.ww; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  all_goals try simp only [eC, eS, hk]
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact hdj.ctx.sub_left (Region.sub_prefix (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · exact (hdj.ok.st.sub_right (Lay.stSub (by decide))).symm
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact hdj.ok.w.sub_right (Lay.wSub (by decide))
  · exact L.kc.sub_right (Region.sub_prefix (by decide))
  · exact L.stk_st (by decide)
  · exact hdj.ok.stk
  · exact L.stk_w (by decide)
  · exact VG.Proof.AesGcm.Arm.covers_prefix he.perm.ctx (by decide)
  · exact VG.Proof.AesGcm.Arm.covers_cons (he.perm.stC (by decide)) (VG.Proof.AesGcm.Arm.covers_cons hdj.wr (he.perm.wC (by decide)))

/-- The arguments of `vg_aes_ctr32` on the keystream block. -/
theorem ctrTail_mk {R : Nat} {s : State} (he : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s)
    (h0 : s.gpr .r0 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 R) (h2 : s.gpr .r2 = st + BitVec.ofNat 32 48)
    (h3 : s.gpr .r3 = st + BitVec.ofNat 32 64) (h12 : s.gpr .r12 = BitVec.ofNat 32 1)
    (hlr : s.gpr .lr = w + BitVec.ofNat 32 512) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    VG.Proof.AesGcm.Arm.CtrCall s c (st + BitVec.ofNat 32 48) (st + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 512) R 1 := by
  have eC := L.stA (d := 48) (by decide)
  have eK := L.stA (d := 64) (by decide)
  have eS := L.wA (d := 512) (by decide)
  have hk := he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, by rw [hk]; exact L.sp8, by have := L.cw; omega,
    by rw [L.stN (by decide)]; have := L.sw; omega, by rw [L.stN (by decide)]; have := L.sw; omega,
    by rw [L.wN (by decide)]; have := L.ww; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [eC, eK, eS, hk]
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact (L.cs.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.stSub (by decide))
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
  · exact L.kc.sub_right (Region.sub_prefix (by decide))
  · exact L.stk_st (by decide)
  · exact L.stk_st (by decide)
  · exact L.stk_w (by decide)
  · exact VG.Proof.AesGcm.Arm.covers_prefix he.perm.ctx (by decide)
  · exact VG.Proof.AesGcm.Arm.covers_cons (he.perm.stC (by decide)) (VG.Proof.AesGcm.Arm.covers_cons (he.perm.stC (by decide))
      (he.perm.wC (by decide)))

/-- Whole blocks. -/
theorem cryptWhole_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.CrMid c st w sp k7 k8 R icb P D n m₀ j s) (hc : VG.Proof.AesGcm.Arm.ciphOf s.mem (State.addr c) R = VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R) :
    WP isa cryptWhole s (fun s' => ∃ j', j' = j + 16 * ((n - j) / 16) ∧ VG.Proof.AesGcm.Arm.CrMid c st w sp k7 k8 R icb P D n m₀ j' s' ∧
      n - j' < 16) := by
  have hn' := h.data.ok.lt32
  have he := h.env
  obtain ⟨s₁, run₁, h3, h12, h4, h5, hz, hg₁, hk₁⟩ := VG.Proof.AesGcm.Arm.splitCtr_ok h.le hn' h.r4 h.r5
  generalize hnb : (n - j) / 16 = nb at h12 h4 h5 hz
  have h16 : 16 * nb ≤ n - j := by omega
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) hk₁.sp hk₁.rd hk₁.wr
  have hd₁ : VG.Proof.AesGcm.Arm.DataW c st w sp k7 k8 s₁ D n := h.data.of_eq hk₁.rd hk₁.wr
  have r8₁ : s₁.gpr .r8 = BitVec.ofNat 32 R := by
    rw [hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r8]
  refine WP.ite (decide (nb = 0)) (VG.Proof.AesGcm.Arm.eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine WP.block_nil ⟨j, by omega, ⟨he₁, h.le, by rw [h4]; rfl, by rw [h5]; rfl, r8₁, h.rounds, hd₁,
      fun hc₀ => by rw [hk₁.mem]; exact h.ctr hc₀, fun hc₀ => by rw [hk₁.mem]; exact h.done hc₀,
      by rw [hk₁.mem]; exact h.rest, h.whole, by rw [hk₁.mem]; exact h.frame⟩, by omega⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hw : (P + j) % 16 = 0 := h.whole.resolve_left (by omega)
    have hdj := h.data.sub (j := j) (k := 16 * nb) (by omega) (by omega)
    have eD := h.data.ok.addr (j := j) (by omega)
    obtain ⟨s₂, run₂, h0', h1', h2', hlr', hg₂, hk₂⟩ := VG.Proof.AesGcm.Arm.wholeArgs_ok he₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he₂ : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s₂ := he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide) (by decide) (by decide))
      hk₂.sp hk₂.rd hk₂.wr
    have eC := L.stA (d := 48) (by decide)
    have eS := L.wA (d := 512) (by decide)
    have hk := he₂.sp
    have hcall : VG.Proof.AesGcm.Arm.CtrCall s₂ c (st + BitVec.ofNat 32 48) (D + BitVec.ofNat 32 j) (w + BitVec.ofNat 32 512) R nb :=
      VG.Proof.AesGcm.Arm.ctrWhole_mk L he₂ h0' (by rw [h1', r8₁]) h2' (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h3])
        (by rw [hg₂ _ (by decide) (by decide) (by decide) (by decide), h12]) hlr' h.rounds
        (hdj.of_eq (hk₂.rd.trans hk₁.rd) (hk₂.wr.trans hk₁.wr))
    refine WP.mono (VG.Proof.AesGcm.Arm.ctr_call hcall) fun s₃ g => ?_
    have gout := g.out; have gctr := g.ctr; have gframe := g.frame
    simp only [hk₂.mem, hk₁.mem, eC, eS, eD, hk] at gout gctr gframe
    have hcw := fun hc₀ => Proof.Gcm.ctr_whole (h.ctr hc₀) hw (m' := s₃.mem)
      (dp := State.addr D + BitVec.ofNat 64 j) (nb := nb) (by rw [gout, ← hc]) gctr
    refine ⟨j + 16 * nb, by omega, ⟨he₂.of_saved g.saved g.sp g.rd g.wr, by omega, ?_, ?_, ?_, h.rounds,
      hd₁.of_eq (g.rd.trans hk₂.rd) (g.wr.trans hk₂.wr), ?_, ?_, ?_, .inr (by omega), ?_⟩, by omega⟩
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h4]
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), h5]
    · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide), r8₁]
    · intro hc₀; rw [← Nat.add_assoc]; exact (hcw hc₀).2
    · -- The bytes done.
      intro hc₀
      have hj16 : bytesAt s₃.mem (State.addr D + BitVec.ofNat 64 j) (16 * nb) =
          xorKs (VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R) icb (P + j) (bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (16 * nb)) := by
        rw [(hcw hc₀).1]
        congr 1
        have e := congrArg (List.take (16 * nb)) h.rest
        rwa [show n - j = 16 * nb + (n - j - 16 * nb) by omega, VG.Proof.AesGcm.Arm.bytesAt_add, VG.Proof.AesGcm.Arm.bytesAt_add,
          List.take_left' (VG.Proof.AesGcm.Arm.length_bytesAt _ _ _), List.take_left' (VG.Proof.AesGcm.Arm.length_bytesAt _ _ _)] at e
      have hjd : bytesAt s₃.mem (State.addr D) j = bytesAt s.mem (State.addr D) j := VG.Proof.AesGcm.Arm.bytesAt_frame gframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (h.data.take h.le).ok.st.sub_right (Lay.stSub (by decide))
        · exact VG.Proof.AesGcm.Arm.split_disj (D := State.addr D) (j := j) (n := n) h.le h.data.ok.lt |>.sub_right
            (Region.sub_prefix (by omega))
        · exact (h.data.take h.le).ok.w.sub_right (Lay.wSub (by decide))
        · exact (h.data.take h.le).ok.stk.symm) (by omega)
      exact VG.Proof.AesGcm.Arm.done_append (hjd.trans (h.done hc₀)) hj16
    · -- The bytes left.
      have hdis : ∀ r ∈ [⟨State.addr st + BitVec.ofNat 64 48, 16⟩, ⟨State.addr D + BitVec.ofNat 64 j, 16 * nb⟩,
          ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, VG.Proof.AesGcm.Arm.below sp],
          (⟨State.addr D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ : Region).Disjoint r := by
        have hst := h.data.ok.st; have hW := h.data.ok.w; have hK := h.data.ok.stk
        have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 (j + 16 * nb), n - (j + 16 * nb)⟩ ⟨State.addr D, n⟩ :=
          Offset.sub_base _ (by omega)
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hst.sub_left hs).sub_right (Lay.stSub (by decide))
        · rw [← VG.Proof.AesGcm.Arm.add_ofNat_assoc]
          have := VG.Proof.AesGcm.Arm.split_disj (D := State.addr D + BitVec.ofNat 64 j) (j := 16 * nb) (n := n - j) h16 (by omega)
          rw [show n - j - 16 * nb = n - (j + 16 * nb) by omega] at this
          exact this.symm
        · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
        · exact (hK.sub_right hs).symm
      rw [VG.Proof.AesGcm.Arm.bytesAt_frame gframe hdis (by omega)]
      have e := congrArg (List.drop (16 * nb)) h.rest
      have e₂ : ∀ m : Mem, (bytesAt m (State.addr D + BitVec.ofNat 64 j) (n - j)).drop (16 * nb) =
          bytesAt m (State.addr D + BitVec.ofNat 64 (j + 16 * nb)) (n - (j + 16 * nb)) := fun m => by
        rw [show n - j = 16 * nb + (n - (j + 16 * nb)) by omega, VG.Proof.AesGcm.Arm.bytesAt_add,
          List.drop_left' (VG.Proof.AesGcm.Arm.length_bytesAt _ _ _), VG.Proof.AesGcm.Arm.add_ofNat_assoc]
      simpa only [e₂] using e
    · refine h.frame.trans (gframe.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., (Offset.sub_base _ (by omega))⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- The keystream block zeroed and the arguments of `vg_aes_ctr32` on it. -/
theorem tailArgs_ok {s : State} (he : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa tailArgs s = some s' ∧
      s'.mem = Cmac.store4 s.mem (State.addr st + BitVec.ofNat 64 64) 0 0 0 0 ∧
      s'.gpr .r0 = c ∧ s'.gpr .r1 = s.gpr .r8 ∧ s'.gpr .r2 = st + BitVec.ofNat 32 48 ∧
      s'.gpr .r3 = st + BitVec.ofNat 32 64 ∧ s'.gpr .r12 = BitVec.ofNat 32 1 ∧
      s'.gpr .lr = w + BitVec.ofNat 32 512 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h9 := he.r9; have h10 := he.r10; have h11 := he.r11
  have w₀ := he.perm.stW (show 64 + 4 ≤ 80 by decide)
  have w₁ := he.perm.stW (show 68 + 4 ≤ 80 by decide)
  have w₂ := he.perm.stW (show 72 + 4 ≤ 80 by decide)
  have w₃ := he.perm.stW (show 76 + 4 ≤ 80 by decide)
  refine ⟨_, by simp only [tailArgs]; arun [h10, L.stA, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, VG.Proof.AesGcm.Arm.mem_store, VG.Proof.AesGcm.Arm.store4_eq, VG.Proof.AesGcm.Arm.add_ofNat_assoc]; rfl
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg, h10]
  · simp [gpr_setReg]
  · simp [gpr_setReg, h11]
  · intro r a b d e f i; simp [gpr_setReg, a, b, d, e, f, i]
  all_goals rfl

/-- The last bytes' keystream block, from `vg_aes_ctr32`. -/
structure TailKs (c st w sp k7 k8 : BitVec 32) (R : Nat) (icb : Block) (P : Nat) (D : BitVec 32) (n : Nat) (m₀ : Mem)
    (j : Nat) (s₀ s : State) : Prop where
  mid : VG.Proof.AesGcm.Arm.CrMid c st w sp k7 k8 R icb P D n m₀ j s₀
  env : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s
  r4 : s.gpr .r4 = D + BitVec.ofNat 32 j
  r5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  ks : blockAt s.mem (State.addr st + BitVec.ofNat 64 64) =
    VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R (blockAt s₀.mem (State.addr st + BitVec.ofNat 64 48))
  cb : blockAt s.mem (State.addr st + BitVec.ofNat 64 48) =
    Spec.Gcm.inc32 (blockAt s₀.mem (State.addr st + BitVec.ofNat 64 48))
  frame : Frame [⟨State.addr st + BitVec.ofNat 64 48, 32⟩, ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩, VG.Proof.AesGcm.Arm.below sp]
    s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The new keystream block. -/
theorem tailKs_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.CrMid c st w sp k7 k8 R icb P D n m₀ j s) (hc : VG.Proof.AesGcm.Arm.ciphOf s.mem (State.addr c) R = VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R) :
    WP isa (.seq (.block tailArgs) ctrFrame) s (VG.Proof.AesGcm.Arm.TailKs c st w sp k7 k8 R icb P D n m₀ j s) := by
  have he := h.env
  obtain ⟨s₂, run₂, hm₂, h0, h1, h2, h3, h12, hlr, hg₂, hrd₂, hwr₂, hsp₂⟩ := VG.Proof.AesGcm.Arm.tailArgs_ok L he
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have he₂ : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hsp₂ hrd₂ hwr₂
  have hk := he₂.sp
  have eC := L.stA (d := 48) (by decide)
  have eK := L.stA (d := 64) (by decide)
  have eS := L.wA (d := 512) (by decide)
  have fz : Frame [⟨State.addr st + BitVec.ofNat 64 64, 16⟩] s.mem s₂.mem := by
    rw [hm₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hKS0 : blockAt s₂.mem (State.addr st + BitVec.ofNat 64 64) = 0 := by
    rw [blockAt, hm₂, VG.Proof.AesGcm.Arm.store4_zero_bytes]; decide
  have hCB : blockAt s₂.mem (State.addr st + BitVec.ofNat 64 48) = blockAt s.mem (State.addr st + BitVec.ofNat 64 48) :=
    VG.Proof.AesGcm.Arm.blockAt_frame fz fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by decide)) (by decide) (by decide)
  have hc₂ : VG.Proof.AesGcm.Arm.ciphOf s₂.mem (State.addr c) R = VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R := by
    rw [VG.Proof.AesGcm.Arm.ciph_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.cs.sub_right (Lay.stSub (by decide))) h.rounds, hc]
  have hcall : VG.Proof.AesGcm.Arm.CtrCall s₂ c (st + BitVec.ofNat 32 48) (st + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 512) R 1 :=
    VG.Proof.AesGcm.Arm.ctrTail_mk L he₂ h0 (by rw [h1, h.r8]) h2 h3 h12 hlr h.rounds
  refine WP.mono (VG.Proof.AesGcm.Arm.ctr_call hcall) fun s₃ g => ?_
  have gout := g.out; have gctr := g.ctr; have gframe := g.frame
  simp only [eC, eK, eS, hk] at gout gctr gframe
  rw [VG.Proof.AesGcm.Arm.blocksAt_one, VG.Proof.AesGcm.Arm.blocksAt_one, hKS0, Cmac.ctr32_one, List.cons.injEq] at gout
  refine ⟨h, he₂.of_saved g.saved g.sp g.rd g.wr, ?_, ?_, ?_, ?_, ?_, ?_, by rw [g.rd, hrd₂], by rw [g.wr, hwr₂]⟩
  · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r4]
  · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r5]
  · rw [g.saved _ (by decide) (by decide), hg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r8]
  · rw [gout.1, ← hc₂, hCB]
  · rw [gctr, hCB]; rfl
  · refine (fz.sub fun r hr => ?_).trans (gframe.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩

/-- The last bytes XORed with the new keystream block. -/
theorem tailXor_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s₀ s : State}
    (h : VG.Proof.AesGcm.Arm.TailKs c st w sp k7 k8 R icb P D n m₀ j s₀ s) (hj : n - j < 16) (h0 : n - j ≠ 0) :
    WP isa (.seq (.block [addI .r1 .r10 64, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)]) xorLoop) s
      (VG.Proof.AesGcm.Arm.CrOut c st w sp k7 k8 R icb P D n m₀) := by
  have hm := h.mid
  have hn' := hm.data.ok.lt32
  have hw : (P + j) % 16 = 0 := hm.whole.resolve_left h0
  have hdj := hm.data.sub (j := j) (k := n - j) (by omega) (by omega)
  have eD := hm.data.ok.addr (j := j) (by omega)
  have he₃ := h.env
  obtain ⟨s₄, run₄, h1, h2, h3, hg₄, hk₄⟩ : ∃ s₄, runBlock isa
      [addI .r1 .r10 64, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)] s = some s₄ ∧
      s₄.gpr .r1 = st + BitVec.ofNat 32 64 ∧ s₄.gpr .r2 = D + BitVec.ofNat 32 j ∧
      s₄.gpr .r3 = BitVec.ofNat 32 (n - j) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₄.gpr r = s.gpr r) ∧ VG.Proof.AesGcm.Arm.Keeps s s₄ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he₃.r10]
    · simp [gpr_setReg, h.r4]
    · simp [gpr_setReg, h.r5]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have eK := L.stA (d := 64) (by decide)
  have lp : VG.Proof.AesGcm.Arm.LoopPre s₄ (st + BitVec.ofNat 32 64) (D + BitVec.ofNat 32 j) (n - j) := by
    refine ⟨h1, h2, h3, by omega, by omega, by rw [L.stN (by decide)]; have := L.sw; omega, hdj.ok.fit, ?_, ?_, ?_⟩
    · rw [hk₄.rd, hk₄.wr, eK]; exact VG.Proof.AesGcm.Arm.covers_left (he₃.perm.stC (by omega))
    · rw [hk₄.wr, h.wr]; exact hdj.wr
    · rw [eK]; exact (hdj.ok.st.sub_right (Lay.stSub (by omega))).symm
  refine WP.mono (VG.Proof.AesGcm.Arm.xorLoop_ok s₄ lp) fun s₅ ⟨hm₅, lo⟩ => ?_
  rw [hk₄.mem, eK, eD] at hm₅
  have hxl := VG.Proof.AesGcm.Arm.length_xorBytes s.mem (State.addr D + BitVec.ofNat 64 j) (State.addr st + BitVec.ofNat 64 64) (n - j)
  have fw : Frame [⟨State.addr D + BitVec.ofNat 64 j, n - j⟩] s.mem s₅.mem := by
    rw [hm₅]; exact VG.Proof.AesGcm.Arm.writeBytes_frame' _ hxl
  have dst := hdj.ok.st; have dw := hdj.ok.w; have dk := hdj.ok.stk
  rw [eD] at dst dw dk
  have hd₃ : bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j) =
      bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j) := by
    rw [← hm.rest, VG.Proof.AesGcm.Arm.bytesAt_frame h.frame (fun r hr => ?_) (by omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dst.sub_right (Lay.stSub (by decide))
    · exact dw.sub_right (Lay.wSub (by decide))
    · exact dk.symm
  have ht := fun hc₀ => Proof.Gcm.ctr_tail (hm.ctr hc₀) hw (m₁ := s.mem) h.ks (by rw [h.cb])
    (d := bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j)) (by rw [VG.Proof.AesGcm.Arm.length_bytesAt]; omega)
    (by rw [VG.Proof.AesGcm.Arm.length_bytesAt]; omega)
  rw [VG.Proof.AesGcm.Arm.length_bytesAt] at ht
  have dS : ∀ r ∈ [(⟨State.addr D + BitVec.ofNat 64 j, n - j⟩ : Region)], ∀ k, k + 16 ≤ 80 →
      (⟨State.addr st + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint r := by
    intro r hr k hk; simp only [List.mem_singleton] at hr; subst hr
    exact (dst.sub_right (Lay.stSub hk)).symm
  have g : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₅.gpr r = s.gpr r :=
    fun r a b c d e => by rw [lo.other r a b c d e, hg₄ r b c d]
  refine ⟨he₃.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (lo.sp.trans hk₄.sp) (lo.rd.trans hk₄.rd) (lo.wr.trans hk₄.wr),
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r8], ?_, ?_, ?_⟩
  · intro hc₀
    rw [show P + n = P + j + (n - j) by omega]
    exact (ht hc₀).2.congr (VG.Proof.AesGcm.Arm.blockAt_frame fw fun r hr => dS r hr 48 (by decide))
      (VG.Proof.AesGcm.Arm.blockAt_frame fw fun r hr => dS r hr 64 (by decide))
  · intro hc₀
    have hdone : bytesAt s₅.mem (State.addr D) j = bytesAt s₀.mem (State.addr D) j := by
      have hdt := (hm.data.take hm.le).ok
      rw [VG.Proof.AesGcm.Arm.bytesAt_frame fw (fun r hr => ?_) (by omega), VG.Proof.AesGcm.Arm.bytesAt_frame h.frame (fun r hr => ?_) (by omega)]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hdt.st.sub_right (Lay.stSub (by decide))
        · exact hdt.w.sub_right (Lay.wSub (by decide))
        · exact hdt.stk.symm
      · simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.AesGcm.Arm.split_disj hm.le hm.data.ok.lt
    have hpiece : bytesAt s₅.mem (State.addr D + BitVec.ofNat 64 j) (n - j) =
        xorKs (VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R) icb (P + j) (bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j)) := by
      have e := VG.Proof.AesGcm.Arm.bytesAt_writeBytes_self s.mem (State.addr D + BitVec.ofNat 64 j)
        (VG.Proof.AesGcm.Arm.xorBytes s.mem (State.addr D + BitVec.ofNat 64 j) (State.addr st + BitVec.ofNat 64 64) (n - j))
        (by rw [hxl]; omega)
      rw [hxl] at e
      rw [hm₅, e, VG.Proof.AesGcm.Arm.xorBytes, hd₃, (ht hc₀).1]
    rw [show n = j + (n - j) by omega]
    exact VG.Proof.AesGcm.Arm.done_append (hdone.trans (hm.done hc₀)) hpiece
  · refine hm.frame.trans (Frame.trans (h.frame.sub fun r hr => ?_) (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega)⟩

/-- The last bytes, with a new keystream block. -/
theorem cryptTail_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.CrMid c st w sp k7 k8 R icb P D n m₀ j s) (hj : n - j < 16)
    (hc : VG.Proof.AesGcm.Arm.ciphOf s.mem (State.addr c) R = VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R) :
    WP isa cryptTail s (VG.Proof.AesGcm.Arm.CrOut c st w sp k7 k8 R icb P D n m₀) := by
  have hn' := h.data.ok.lt32
  have he := h.env
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := VG.Proof.AesGcm.Arm.cmp0_ok s .r5 h.r5 (by omega)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ : VG.Proof.AesGcm.Arm.Env c st w sp k7 k8 s₁ := he.keep (fun r _ => by rw [hg₁]) hsp₁ hrd₁ hwr₁
  have h₁ : VG.Proof.AesGcm.Arm.CrMid c st w sp k7 k8 R icb P D n m₀ j s₁ :=
    ⟨he₁, h.le, (by rw [hg₁]; exact h.r4), (by rw [hg₁]; exact h.r5), (by rw [hg₁]; exact h.r8), h.rounds,
      h.data.of_eq hrd₁ hwr₁, (fun hc₀ => by rw [hm₁]; exact h.ctr hc₀), (fun hc₀ => by rw [hm₁]; exact h.done hc₀),
      (by rw [hm₁]; exact h.rest), h.whole, (by rw [hm₁]; exact h.frame)⟩
  refine WP.ite (decide (n - j = 0)) (VG.Proof.AesGcm.Arm.eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by have := h.le; simp at ht; omega
    subst h0
    exact WP.block_nil ⟨he₁, h₁.r8, fun hc₀ => h₁.ctr hc₀, fun hc₀ => h₁.done hc₀, h₁.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    exact WP.seq (WP.mono (VG.Proof.AesGcm.Arm.tailKs_ok L h₁ (by rw [hm₁]; exact hc)) fun _ ht => VG.Proof.AesGcm.Arm.tailXor_ok L ht hj h0)

theorem CrMid.ciph {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {m₀ : Mem} {j : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.CrMid c st w sp k7 k8 R icb P D n m₀ j s) : VG.Proof.AesGcm.Arm.ciphOf s.mem (State.addr c) R = VG.Proof.AesGcm.Arm.ciphOf m₀ (State.addr c) R :=
  VG.Proof.AesGcm.Arm.ciph_frame h.frame (VG.Proof.AesGcm.Arm.ctx_crFrame L h.data) h.rounds

omit L in
theorem CrIn.keep {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s s' : State}
    (h : VG.Proof.AesGcm.Arm.CrIn c st w sp k7 k8 R icb P D n s) (hg : s'.gpr = s.gpr) (hk : VG.Proof.AesGcm.Arm.Keeps s s') : VG.Proof.AesGcm.Arm.CrIn c st w sp k7 k8 R icb P D n s' :=
  ⟨h.env.keep (fun r _ => by rw [hg]) hk.sp hk.rd hk.wr, by rw [hg]; exact h.r4, by rw [hg]; exact h.r5,
    by rw [hg]; exact h.r6, by rw [hg]; exact h.r8, h.rounds, h.data.of_eq hk.rd hk.wr⟩

/-- The rest of the keystream block first, if there is one. -/
theorem cryptFill_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.CrIn c st w sp k7 k8 R icb P D n s) (h0 : n ≠ 0) :
    WP isa cryptFill s (fun s' => ∃ j, j = (if P % 16 = 0 then 0 else min (16 - P % 16) n) ∧
      VG.Proof.AesGcm.Arm.CrMid c st w sp k7 k8 R icb P D n s.mem j s') := by
  obtain ⟨s₂, run₂, hz₂, hg₂, hm₂, hrd₂, hwr₂, hsp₂⟩ := VG.Proof.AesGcm.Arm.cmp0_ok s .r6 h.r6
    (by have := Nat.mod_lt P (show 16 > 0 by decide); omega)
  have h₂ := h.keep hg₂ ⟨hm₂, hrd₂, hwr₂, hsp₂⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.ite (decide (P % 16 = 0)) (VG.Proof.AesGcm.Arm.eval_eq' hz₂) (fun ht => ?_) (fun hf => ?_)
  · have ho : P % 16 = 0 := by simpa using ht
    exact WP.block_nil ⟨0, by simp [ho], h₂.env, by omega, by rw [h₂.r4, VG.Proof.AesGcm.Arm.add_ofNat_zero], by rw [h₂.r5, Nat.sub_zero], h₂.r8,
      h₂.rounds, h₂.data, fun hc₀ => by rw [hm₂]; simpa using hc₀, fun _ => by simp [bytesAt]; rfl,
      by rw [hm₂, VG.Proof.AesGcm.Arm.add_ofNat_zero], .inr (by omega), by rw [hm₂]; exact Frame.refl _ _⟩
  · have hP : P % 16 ≠ 0 := by simpa using hf
    have := VG.Proof.AesGcm.Arm.cryptHead_ok L h₂ h0 hP
    rw [hm₂] at this
    exact WP.mono this fun _ ⟨j, hj, hm⟩ => ⟨j, by simp only [hP, ite_false]; exact hj, hm⟩

/-- `crypt`. -/
theorem crypt_ok {R : Nat} {icb : Block} {P : Nat} {D : BitVec 32} {n : Nat} {s : State}
    (h : VG.Proof.AesGcm.Arm.CrIn c st w sp k7 k8 R icb P D n s) :
    WP isa crypt s (VG.Proof.AesGcm.Arm.CrOut c st w sp k7 k8 R icb P D n s.mem) := by
  have hn' := h.data.ok.lt32
  obtain ⟨s₁, run₁, hz, hg₁, hm₁, hrd₁, hwr₁, hsp₁⟩ := VG.Proof.AesGcm.Arm.cmp0_ok s .r5 h.r5 hn'
  have h₁ := h.keep hg₁ ⟨hm₁, hrd₁, hwr₁, hsp₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (VG.Proof.AesGcm.Arm.eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨h₁.env, h₁.r8, fun hc₀ => by rw [hm₁]; exact hc₀,
      fun _ => by simp [bytesAt]; rfl, by rw [hm₁]; exact Frame.refl _ _⟩
  · have h0 : n ≠ 0 := by simpa using hf
    rw [← hm₁]
    refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.cryptFill_ok L h₁ h0) fun s' ⟨j, _, hj⟩ => ?_)
    refine WP.seq (WP.mono (VG.Proof.AesGcm.Arm.cryptWhole_ok L hj (hj.ciph L)) fun s'' ⟨j', _, hj', hlt⟩ => ?_)
    exact VG.Proof.AesGcm.Arm.cryptTail_ok L hj' hlt (hj'.ciph L)

end

end VG.Proof.AesGcm.Arm

end
