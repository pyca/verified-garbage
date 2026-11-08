module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyVecBytes
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyGroups
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyCopy
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyWords
import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeySetup
import VerifiedGarbage.Proof.Framework.CountedLoop
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the vector loops of 16- and 32-byte keys.
/-! # POWER8 AES key expansion, four words at a time

The instruction groups of the vector loops, each run once symbolically, and
the loops' invariants: `v1` (and `v2`) hold the last four (eight) words of
the schedule so far as `Rk` says, and the schedule up to there is in memory.
-/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Impl.Aes.PPC64LE.Crypto (rotCtl subCtl rcCtl)
open VG.Proof.Aes.KeyWords (W Good W_ge temp32 sub32)
open VG.Impl.Aes.KeyWords (rc)

/-- The vector constants and `r12 = 0`. -/
structure VConst (s : State) : Prop where
  zero : s.vpr .v4 = 0
  rot : s.vpr .v5 = rotCtl ++ rotCtl
  sub : s.vpr .v6 = subCtl ++ subCtl
  rc : s.vpr .v7 = rcCtl ++ rcCtl
  r12 : s.gpr .r12 = 0

theorem VConst.of_local {s t : State} {gs : List Reg} {vs : List VReg} (h : VConst s) (hl : Local gs vs s t)
    (hg : .r12 ∉ gs) (hv : .v4 ∉ vs ∧ .v5 ∉ vs ∧ .v6 ∉ vs ∧ .v7 ∉ vs) : VConst t :=
  ⟨(hl.v _ hv.1).trans h.zero, (hl.v _ hv.2.1).trans h.rot, (hl.v _ hv.2.2.1).trans h.sub,
    (hl.v _ hv.2.2.2).trans h.rc, (hl.keep.gpr hg).trans h.r12⟩

theorem VConst.of_keep {s t : State} {gs : List Reg} (h : VConst s) (hk : Keep gs s t) (hg : .r12 ∉ gs)
    (hv : ∀ r, r = .v4 ∨ r = .v5 ∨ r = .v6 ∨ r = .v7 → t.vpr r = s.vpr r) : VConst t :=
  ⟨(hv _ (by simp)).trans h.zero, (hv _ (by simp)).trans h.rot, (hv _ (by simp)).trans h.sub,
    (hv _ (by simp)).trans h.rc, (hk.gpr hg).trans h.r12⟩

theorem shl_eq (x : BitVec 128) (sh : Nat) : ((x ++ (0 : BitVec 128)) <<< (8 * sh)).extractLsb' 128 128 = shl x sh :=
  rfl

theorem prefixXor_ok (d : VReg) (s : State) (hd : d ≠ .v3 ∧ d ≠ .v4) (hz : s.vpr .v4 = 0) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.prefixXor d)) s fun t =>
      t.vpr d = pfx (s.vpr d) ∧ Local [] [.v3, d] s t := by
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.prefixXor, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    reduceVOpEval, Option.map_some, vpr_writeV, hd.1, Ne.symm hd.1, Ne.symm hd.2, ite_true, ite_false,
    reduceCtorEq, show (4 : Nat) < 16 by decide, show (8 : Nat) < 16 by decide, hz, shl_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ((Local.writeV _ _ _).trans ((Local.writeV _ _ _).trans ((Local.writeV _ _ _).trans
    (Local.writeV _ _ _)))).weaken (by simp) (by simp)⟩

theorem stepRot_ok (d t : VReg) (s : State) (hd : d ≠ .v0 ∧ d ≠ .v3 ∧ d ≠ .v4 ∧ d ≠ .v8)
    (hz : s.vpr .v4 = 0) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.stepRot d t)) s fun u =>
      u.vpr d = pfx (s.vpr d) ^^^ (sboxV (permSelf (s.vpr t) (s.vpr .v5)) ^^^ s.vpr .v8) ∧
        Local [] [.v0, .v3, d] s u := by
  rw [Impl.Aes.PPC64LE.Crypto.stepRot, WP.block_append_iff, WP.block_append_iff]
  have h1 : WP isa (.block [.vop (.perm .v0 t t .v5), .vop (.sbox .v0 .v0), .vop (.logic .xor .v0 .v0 .v8)]) s
      fun u => u.vpr .v0 = sboxV (permSelf (s.vpr t) (s.vpr .v5)) ^^^ s.vpr .v8 ∧ Local [] [.v0] s u := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, reduceVOpEval, Option.map_some,
      vpr_writeV, ite_true, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
    exact ⟨rfl, ((Local.writeV _ _ _).trans ((Local.writeV _ _ _).trans (Local.writeV _ _ _))).weaken
      (by simp) (by simp)⟩
  refine WP.mono h1 fun u ⟨hu, lu⟩ => ?_
  refine WP.mono (prefixXor_ok d u ⟨hd.2.1, hd.2.2.1⟩ ((lu.v _ (by decide)).trans hz)) fun w ⟨hw, lw⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, reduceVOpEval, Option.map_some,
    vpr_writeV, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ((lu.trans lw).trans (Local.writeV _ _ _)).weaken (by simp) (by simp)⟩
  rw [hw, lw.v .v0 (by simp [Ne.symm hd.1]), hu, lu.v d (by simp [hd.1])]

theorem stepSub_ok (d t : VReg) (s : State) (hd : d ≠ .v0 ∧ d ≠ .v3 ∧ d ≠ .v4)
    (hz : s.vpr .v4 = 0) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.stepSub d t)) s fun u =>
      u.vpr d = pfx (s.vpr d) ^^^ sboxV (permSelf (s.vpr t) (s.vpr .v6)) ∧ Local [] [.v0, .v3, d] s u := by
  rw [Impl.Aes.PPC64LE.Crypto.stepSub, WP.block_append_iff, WP.block_append_iff]
  have h1 : WP isa (.block [.vop (.perm .v0 t t .v6), .vop (.sbox .v0 .v0)]) s
      fun u => u.vpr .v0 = sboxV (permSelf (s.vpr t) (s.vpr .v6)) ∧ Local [] [.v0] s u := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, reduceVOpEval, Option.map_some,
      vpr_writeV, ite_true, Option.some.injEq, exists_eq_left']
    exact ⟨rfl, ((Local.writeV _ _ _).trans (Local.writeV _ _ _)).weaken (by simp) (by simp)⟩
  refine WP.mono h1 fun u ⟨hu, lu⟩ => ?_
  refine WP.mono (prefixXor_ok d u ⟨hd.2.1, hd.2.2⟩ ((lu.v _ (by decide)).trans hz)) fun w ⟨hw, lw⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, reduceVOpEval, Option.map_some,
    vpr_writeV, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ((lu.trans lw).trans (Local.writeV _ _ _)).weaken (by simp) (by simp)⟩
  rw [hw, lw.v .v0 (by simp [Ne.symm hd.1]), hu, lu.v d (by simp [hd.1])]

theorem rcSplat_ok (s : State) {c : BitVec 8} (hc : s.gpr .r6 = c.setWidth 64) (hk : VConst s) :
    WP isa (.block Impl.Aes.PPC64LE.Crypto.rcSplat) s fun u =>
      (∀ i < 16, vbyte (u.vpr .v8) i = if i % 4 = 3 then c else 0#8) ∧ Local [] [.v8] s u := by
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.rcSplat, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    reduceVOpEval, Option.map_some, vpr_writeV, ite_true, reduceCtorEq, ite_false, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun i hi => ?_, ⟨⟨fun r _ => rfl, rfl, rfl⟩, fun r hr => ?_, rfl⟩⟩
  · rw [hk.zero, hk.rc, hc]
    exact rc_splat c _ hi
  · simp only [List.mem_singleton] at hr
    simp only [vpr_writeV, hr, ite_false]

theorem rcStep_ok (s : State) : WP isa (.block Impl.Aes.PPC64LE.Crypto.rcStep) s fun t =>
    t.gpr .r6 = rcNext (s.gpr .r6) ∧ Local [.r0, .r6, .r8] [] s t := by
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.rcStep, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    State.read, Size.ext, Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write, reduceCtorEq,
    ite_true, ite_false, show 7 < 64 by decide,
    show 0 < 2^15 by decide, show 27 < 2^15 by decide, show 255 < 2^15 by decide,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun r _ => ?_, ?_⟩⟩
  · simp only [rcNext, BitVec.ofNat_eq_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [vpr_write]
  · simp only [RegUpd.mem_write]

theorem storeKey_ok (d : VReg) (s : State) (h12 : s.gpr .r12 = 0)
    (hw : InRegions s.wr (s.gpr .r5) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.storeKey d)) s fun u =>
      u.mem = s.mem.write (s.gpr .r5) 16 (s.vpr d) ∧ u.gpr .r5 = s.gpr .r5 + 16#64 ∧
        Keep [.r5] s u ∧ (∀ r, r ≠ .v9 → u.vpr r = s.vpr r) := by
  have hw' : InRegions s.wr (s.gpr .r5 + s.gpr .r12) 16 := by rw [h12]; simpa using hw
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.storeKey, runBlock_cons, runStep_some, exec_sldoi8]
  rw [exec_stxvd2x .v9 .r5 .r12 _ (by decide) (by simpa only [wr_writeV, gpr_writeV] using hw')]
  simp only [runStep_some, runBlock_cons, runBlock_nil, reduceExec, gpr_writeV, vpr_writeV, mem_writeV,
    rd_writeV, wr_writeV, h12, Option.some.injEq, exists_eq_left', show (16 : Nat) < 2^15 by decide, ite_true,
    ne_eq, reduceCtorEq, not_false_eq_true, and_self]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, fun r hr => ?_⟩
  · rw [RegUpd.mem_write, sldoi8_self, swapDwords_involutive]
    simp
  · rw [RegUpd.gpr_write_self]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [vpr_write, vpr_writeV, hr, ite_false]

/-- What a round leaves: the four new words in `d`, stored at `r5`. -/
structure RoundOut (d : VReg) (y : BitVec 128) (s u : State) : Prop where
  key : u.vpr d = pfx (s.vpr d) ^^^ y
  mem : u.mem = s.mem.write (s.gpr .r5) 16 (u.vpr d)
  out : u.gpr .r5 = s.gpr .r5 + 16#64
  keep : Keep [.r0, .r5, .r6, .r8] s u
  v : ∀ r, r ≠ .v0 → r ≠ .v3 → r ≠ .v8 → r ≠ .v9 → r ≠ d → u.vpr r = s.vpr r

theorem rotRound_ok (d t : VReg) (s : State) (hd : d ≠ .v0 ∧ d ≠ .v3 ∧ d ≠ .v4 ∧ d ≠ .v8 ∧ d ≠ .v9)
    (ht : t ≠ .v8) (hk : VConst s) {c : BitVec 8} (hc : s.gpr .r6 = c.setWidth 64)
    (hw : InRegions s.wr (s.gpr .r5) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.rotRound d t)) s fun u => u.gpr .r6 = rcNext (s.gpr .r6) ∧
      ∃ R, (∀ i < 16, vbyte R i = if i % 4 = 3 then c else 0#8) ∧
        RoundOut d (sboxV (permSelf (s.vpr t) (rotCtl ++ rotCtl)) ^^^ R) s u := by
  rw [Impl.Aes.PPC64LE.Crypto.rotRound, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (rcSplat_ok s hc hk) fun u₁ ⟨hR, l₁⟩ => ?_
  refine WP.mono (rcStep_ok u₁) fun u₂ ⟨h6, l₂⟩ => ?_
  have l₁₂ := l₁.trans l₂
  refine WP.mono (stepRot_ok d t u₂ ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1⟩
    ((l₁₂.v _ (by decide)).trans hk.zero)) fun u₃ ⟨h3, l₃⟩ => ?_
  have l₁₃ := l₁₂.trans l₃
  refine WP.mono (storeKey_ok d u₃ ((l₁₃.keep.gpr (by decide)).trans hk.r12)
    (by rw [l₁₃.keep.2.2, l₁₃.keep.gpr (by decide)]; exact hw)) fun u ⟨hm, h5, hk5, hv⟩ => ?_
  refine ⟨?_, u₂.vpr .v8, fun i hi => by rw [l₂.v _ (by simp)]; exact hR i hi, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk5.gpr (by decide), l₃.keep.gpr (by decide), h6, l₁.keep.gpr (by decide)]
  · rw [hv d hd.2.2.2.2, h3, l₁₂.v d (by simp [hd.2.2.2.1]), l₁₂.v t (by simp [ht]),
      (l₁₂.v .v5 (by simp)).trans hk.rot]
  · rw [hm, hv d (Ne.symm (Ne.symm hd.2.2.2.2)), l₁₃.mem, l₁₃.keep.gpr (by decide)]
  · rw [h5, l₁₃.keep.gpr (by decide)]
  · exact (l₁₃.keep.trans hk5).mono (by simp)
  · intro r h0 h3' h8 h9 hdr
    rw [hv r h9, l₁₃.v r (by simp [h0, h3', h8, hdr])]

theorem subRound_ok (d t : VReg) (s : State) (hd : d ≠ .v0 ∧ d ≠ .v3 ∧ d ≠ .v4 ∧ d ≠ .v9)
    (hk : VConst s) (hw : InRegions s.wr (s.gpr .r5) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.stepSub d t ++ Impl.Aes.PPC64LE.Crypto.storeKey d)) s fun u =>
      RoundOut d (sboxV (permSelf (s.vpr t) (subCtl ++ subCtl))) s u ∧ u.gpr .r6 = s.gpr .r6 := by
  rw [WP.block_append_iff]
  refine WP.mono (stepSub_ok d t s ⟨hd.1, hd.2.1, hd.2.2.1⟩ hk.zero) fun u₃ ⟨h3, l₃⟩ => ?_
  refine WP.mono (storeKey_ok d u₃ ((l₃.keep.gpr (by decide)).trans hk.r12)
    (by rw [l₃.keep.2.2, l₃.keep.gpr (by decide)]; exact hw)) fun u ⟨hm, h5, hk5, hv⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hv d hd.2.2.2, h3, hk.sub]
  · rw [hm, hv d (Ne.symm (Ne.symm hd.2.2.2)), l₃.mem, l₃.keep.gpr (by decide)]
  · rw [h5, l₃.keep.gpr (by decide)]
  · exact (l₃.keep.trans hk5).mono (by simp)
  · intro r h0 h3' _ h9 hdr
    rw [hv r h9, l₃.v r (by simp [h0, h3', hdr])]
  · rw [hk5.gpr (by decide), l₃.keep.gpr (by decide)]

/-! ## The recurrence, four words at a time -/

theorem w_rot {m : Mem} {P : Addr} {nk j : Nat} (h3 : nk = 4 ∨ nk = 8) (hj : j % nk = 0) :
    W m P nk (j + nk) = W m P nk j ^^^
      ((sub32 (W m P nk (j + nk - 1))).rotateRight 8 ^^^ (rc (j / nk + 1)).setWidth 32) := by
  rw [W_ge (by omega) (by omega), Nat.add_sub_cancel, temp32, ite_eq_left (by rcases h3 with rfl | rfl <;> omega),
    show (j + nk) / nk = j / nk + 1 by rcases h3 with rfl | rfl <;> omega]

theorem w_sub {m : Mem} {P : Addr} {j : Nat} (hj : j % 8 = 4) :
    W m P 8 (j + 8) = W m P 8 j ^^^ sub32 (W m P 8 (j + 8 - 1)) := by
  rw [W_ge (by omega) (by omega), Nat.add_sub_cancel, temp32, ite_eq_right (by omega),
    ite_eq_left ⟨by decide, by omega⟩]

theorem w_lin {m : Mem} {P : Addr} {nk j : Nat} (h3 : nk = 4 ∨ nk = 8) (hj : j % 4 = 0) :
    ∀ k, 0 < k → k < 4 → W m P nk (j + nk + k) = W m P nk (j + k) ^^^ W m P nk (j + nk + k - 1) := by
  intro k hk0 hk
  rw [W_ge (by omega) (by omega), show j + nk + k - nk = j + k by omega, temp32,
    ite_eq_right (by rcases h3 with rfl | rfl <;> omega), ite_eq_right (by rcases h3 with rfl | rfl <;> omega)]

/-! ## 16-byte keys -/

theorem subi4_ok (s : State) : WP isa (.block [.subi .r4 .r4 1]) s (· = s.write .r4 (s.gpr .r4 - BitVec.ofNat 64 1)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_subi (show Reg.r4 ≠ .r0 by decide) (show 1 ≤ 2^15 by decide), runStep_some,
    runBlock_nil, Option.some.injEq, exists_eq_left']

theorem schedule_wr {base s : State} {P S : Addr} {K : Nat} (hc : KeyConfig base P S K) (hk : Keep keyGprs base s)
    {d : Nat} (hd : d + 16 ≤ 240) : InRegions s.wr (S + BitVec.ofNat 64 d) 16 := by
  rw [hk.2.2]
  exact ⟨⟨S, 240⟩, hc.schedule, Offset.contains_base _ (by omega) (by omega)⟩

structure VInv4 (base : State) (P S : Addr) (r : Nat) (s : State) : Prop where
  bound : r ≤ 10
  keep : Keep keyGprs base s
  cst : VConst s
  out : s.gpr .r5 = S + BitVec.ofNat 64 (16 * r + 16)
  left : s.gpr .r4 = BitVec.ofNat 64 (10 - r)
  rcon : s.gpr .r6 = (rc (r + 1)).setWidth 64
  key : Rk (W base.mem P 4) (4 * r) (s.vpr .v1)
  good : Good s.mem S (W base.mem P 4) (4 * r + 4)
  frame : Frame [⟨S, 240⟩] base.mem s.mem

theorem rot_next {m : Mem} {P : Addr} {nk j : Nat} (h3 : nk = 4 ∨ nk = 8) (hj : j % nk = 0) :
    ∀ k < 4, W m P nk (j + nk + k) =
      ((sub32 (W m P nk (j + nk - 1))).rotateRight 8 ^^^ (rc (j / nk + 1)).setWidth 32) ^^^
        Proof.Aes.PPC64LE.Crypto.pre (W m P nk) j k :=
  next_pre (w_rot h3 hj) (w_lin h3 (by rcases h3 with rfl | rfl <;> omega))

theorem vstep4 {base s : State} {P S : Addr} {r : Nat} (hc : KeyConfig base P S 16) (h : VInv4 base P S r s)
    (hr : r < 10) : WP isa (.block Impl.Aes.PPC64LE.Crypto.body128) s (VInv4 base P S (r + 1)) := by
  rw [Impl.Aes.PPC64LE.Crypto.body128, WP.block_append_iff]
  refine WP.mono (rotRound_ok .v1 .v1 s (by decide) (by decide) h.cst h.rcon
    (by rw [h.out]; exact schedule_wr hc h.keep (by omega))) fun u ⟨h6, R, hR, o⟩ => ?_
  refine WP.mono (subi4_ok u) fun v hv => ?_
  subst hv
  have lw := Local.write u .r4 (u.gpr .r4 - BitVec.ofNat 64 1)
  have hkey : Rk (W base.mem P 4) (4 * (r + 1)) (u.vpr .v1) := by
    rw [o.key, show 4 * (r + 1) = 4 * r + 4 by omega]
    refine step_rk h.key (rot_temp h.key hR) ?_
    have e := rot_next (m := base.mem) (P := P) (nk := 4) (j := 4 * r) (by decide) (by omega)
    rwa [show 4 * r + 4 - 1 = 4 * r + 3 by omega, show 4 * r / 4 + 1 = r + 1 by omega] at e
  have lk : Keep ([.r0, .r5, .r6, .r8] ++ [.r4]) s (u.write .r4 (u.gpr .r4 - BitVec.ofNat 64 1)) :=
    o.keep.trans lw.keep
  have lv : ∀ x, x ≠ .v0 → x ≠ .v3 → x ≠ .v8 → x ≠ .v9 → x ≠ .v1 →
      (u.write .r4 (u.gpr .r4 - BitVec.ofNat 64 1)).vpr x = s.vpr x := fun x a b c d e => by
    rw [lw.v x (by simp)]; exact o.v x a b c d e
  have hcst : VConst (u.write .r4 (u.gpr .r4 - BitVec.ofNat 64 1)) :=
    h.cst.of_keep lk (by simp) fun x hx => by
      rcases hx with rfl | rfl | rfl | rfl <;> exact lv _ (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨by omega, (h.keep.trans lk).mono (by simp [keyGprs]), hcst, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lw.keep.gpr (by decide), o.out, h.out, Offset.add_add]
    exact congrArg (fun k => S + BitVec.ofNat 64 k) (by omega)
  · rw [RegUpd.gpr_write_self, o.keep.gpr (by decide), h.left, Offset.ofNat_sub_ofNat (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [lw.keep.gpr (by decide), h6, h.rcon]
    exact rcNext_rc ⟨r + 1, by omega⟩ (by simp)
  · rw [lw.v .v1 (by simp)]; exact hkey
  · rw [lw.mem, o.mem, h.out, show 16 * r + 16 = 4 * (4 * r + 4) by omega, show 4 * (r + 1) + 4 = 4 * r + 4 + 4 by omega]
    exact store_good h.good (by rw [show 4 * r + 4 = 4 * (r + 1) by omega]; exact hkey) (by omega)
  · rw [lw.mem, o.mem, h.out]
    exact h.frame.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem loop128_ok {base s : State} {P S : Addr} (hc : KeyConfig base P S 16) (h : VInv4 base P S 0 s) :
    WP isa (.loop (.block Impl.Aes.PPC64LE.Crypto.body128) (.nonzero .d .r4)) s (VInv4 base P S 10) := by
  have step : ∀ j t, j+1 ≤ 10 → VInv4 base P S j t →
      WP isa (.block Impl.Aes.PPC64LE.Crypto.body128) t (VInv4 base P S (j+1)) :=
    fun _ _ hj ht => vstep4 hc ht (by omega)
  have test : ∀ j t, j ≤ 10 → VInv4 base P S j t →
      (10-j < 1 → eval (.nonzero .d .r4) t = some false) ∧
      (1 ≤ 10-j → eval (.nonzero .d .r4) t = some true) := by
    intro j t hj ht
    have he := eval_nonzero_ofNat' t .r4 (by omega) ht.left
    change eval (.nonzero .d .r4) t = some (decide (10-j ≠ 0)) at he
    constructor
    · intro hl
      rw [he, show 10-j = 0 by omega]
      rfl
    · intro hl
      rw [he]
      simp only [ne_eq, show ¬10-j = 0 by omega, not_false_eq_true, decide_true]
  refine WP.mono (WP.chunk_loop (by decide) (by omega) h step test) ?_
  rintro t ⟨j, hj, he, ht⟩
  have hje : j = 10 := by omega
  exact hje ▸ ht

/-! ## 32-byte keys -/

structure VInv8 (base : State) (P S : Addr) (i : Nat) (s : State) : Prop where
  bound : i ≤ 6
  keep : Keep keyGprs base s
  cst : VConst s
  out : s.gpr .r5 = S + BitVec.ofNat 64 (32 * i + 32)
  left : s.gpr .r4 = BitVec.ofNat 64 (6 - i)
  rcon : s.gpr .r6 = (rc (i + 1)).setWidth 64
  keyA : Rk (W base.mem P 8) (8 * i) (s.vpr .v1)
  keyB : Rk (W base.mem P 8) (8 * i + 4) (s.vpr .v2)
  good : Good s.mem S (W base.mem P 8) (8 * i + 8)
  frame : Frame [⟨S, 240⟩] base.mem s.mem

theorem sub_next {m : Mem} {P : Addr} {j : Nat} (hj : j % 8 = 4) :
    ∀ k < 4, W m P 8 (j + 8 + k) = sub32 (W m P 8 (j + 8 - 1)) ^^^ Proof.Aes.PPC64LE.Crypto.pre (W m P 8) j k :=
  next_pre (w_sub hj) (w_lin (by decide) (by omega))

/-- The four words after `8 i + 8`, from `v1` and `v2`. -/
theorem keyA_next {base s u : State} {P : Addr} {i : Nat} {R : BitVec 128}
    (hA : Rk (W base.mem P 8) (8 * i) (s.vpr .v1)) (hB : Rk (W base.mem P 8) (8 * i + 4) (s.vpr .v2))
    (hR : ∀ k < 16, vbyte R k = if k % 4 = 3 then rc (i + 1) else 0#8)
    (o : RoundOut .v1 (sboxV (permSelf (s.vpr .v2) (rotCtl ++ rotCtl)) ^^^ R) s u) :
    Rk (W base.mem P 8) (8 * i + 8) (u.vpr .v1) := by
  rw [o.key]
  refine step_rk hA (by simpa only [show 8 * i + 4 + 3 = 8 * i + 8 - 1 by omega] using rot_temp hB hR) ?_
  have e := rot_next (m := base.mem) (P := P) (nk := 8) (j := 8 * i) (by decide) (by omega)
  rwa [show 8 * i / 8 + 1 = i + 1 by omega] at e

theorem vstep8 {base s : State} {P S : Addr} {i : Nat} (hc : KeyConfig base P S 32) (h : VInv8 base P S i s)
    (hi : i < 6) : WP isa (.block Impl.Aes.PPC64LE.Crypto.body256) s (VInv8 base P S (i + 1)) := by
  rw [Impl.Aes.PPC64LE.Crypto.body256, WP.block_append_iff, List.append_assoc, WP.block_append_iff]
  refine WP.mono (rotRound_ok .v1 .v2 s (by decide) (by decide) h.cst h.rcon
    (by rw [h.out]; exact schedule_wr hc h.keep (by omega))) fun u ⟨h6, R, hR, o⟩ => ?_
  have hA := keyA_next h.keyA h.keyB hR o
  have hku : Keep keyGprs base u := (h.keep.trans o.keep).mono (by simp [keyGprs])
  have hcu : VConst u := h.cst.of_keep o.keep (by simp) fun x hx => by
    rcases hx with rfl | rfl | rfl | rfl <;> exact o.v _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5u : u.gpr .r5 = S + BitVec.ofNat 64 (32 * i + 48) := by
    rw [o.out, h.out, Offset.add_add]
  have hgu : Good u.mem S (W base.mem P 8) (8 * i + 12) := by
    rw [o.mem, h.out, show 32 * i + 32 = 4 * (8 * i + 8) by omega]
    exact store_good h.good hA (by omega)
  have hfu : Frame [⟨S, 240⟩] base.mem u.mem := by
    rw [o.mem, h.out]
    exact h.frame.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  refine WP.mono (subRound_ok .v2 .v1 u (by decide) hcu (by rw [h5u]; exact schedule_wr hc hku (by omega)))
    fun w ⟨o', h6'⟩ => ?_
  have hB : Rk (W base.mem P 8) (8 * (i + 1) + 4) (w.vpr .v2) := by
    rw [o'.key, show 8 * (i + 1) + 4 = 8 * i + 4 + 8 by omega,
      o.v .v2 (by decide) (by decide) (by decide) (by decide) (by decide)]
    refine step_rk h.keyB (by simpa only [show 8 * i + 8 + 3 = 8 * i + 4 + 8 - 1 by omega] using sub_temp hA) ?_
    exact sub_next (by omega)
  refine WP.mono (subi4_ok w) fun v hv => ?_
  subst hv
  have lw := Local.write w .r4 (w.gpr .r4 - BitVec.ofNat 64 1)
  have hkw := o'.keep.trans lw.keep
  refine ⟨by omega, (hku.trans hkw).mono (by simp [keyGprs]), hcu.of_keep hkw (by simp) fun x hx => by
      rw [lw.v x (by simp)]
      rcases hx with rfl | rfl | rfl | rfl <;> exact o'.v _ (by decide) (by decide) (by decide) (by decide) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lw.keep.gpr (by decide), o'.out, h5u, Offset.add_add]
    exact congrArg (fun k => S + BitVec.ofNat 64 k) (by omega)
  · rw [RegUpd.gpr_write_self, o'.keep.gpr (by decide), o.keep.gpr (by decide), h.left,
      Offset.ofNat_sub_ofNat (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [lw.keep.gpr (by decide), h6', h6, h.rcon]
    exact rcNext_rc ⟨i + 1, by omega⟩ (by simp)
  · rw [lw.v .v1 (by simp), o'.v .v1 (by decide) (by decide) (by decide) (by decide) (by decide),
      show 8 * (i + 1) = 8 * i + 8 by omega]
    exact hA
  · rw [lw.v .v2 (by simp)]; exact hB
  · rw [lw.mem, o'.mem, h5u, show 32 * i + 48 = 4 * (8 * i + 12) by omega,
      show 8 * (i + 1) + 8 = 8 * i + 12 + 4 by omega]
    exact store_good hgu (by rw [show 8 * i + 12 = 8 * (i + 1) + 4 by omega]; exact hB) (by omega)
  · rw [lw.mem, o'.mem, h5u]
    exact hfu.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem loop256_ok {base s : State} {P S : Addr} (hc : KeyConfig base P S 32) (h : VInv8 base P S 0 s) :
    WP isa (.seq (.loop (.block Impl.Aes.PPC64LE.Crypto.body256) (.nonzero .d .r4))
      (.block (Impl.Aes.PPC64LE.Crypto.rotRound .v1 .v2))) s
      (fun t => Keep keyGprs base t ∧ Good t.mem S (W base.mem P 8) 60) := by
  have step : ∀ j t, j+1 ≤ 6 → VInv8 base P S j t →
      WP isa (.block Impl.Aes.PPC64LE.Crypto.body256) t (VInv8 base P S (j+1)) :=
    fun _ _ hj ht => vstep8 hc ht (by omega)
  have test : ∀ j t, j ≤ 6 → VInv8 base P S j t →
      (6-j < 1 → eval (.nonzero .d .r4) t = some false) ∧
      (1 ≤ 6-j → eval (.nonzero .d .r4) t = some true) := by
    intro j t hj ht
    have he := eval_nonzero_ofNat' t .r4 (by omega) ht.left
    change eval (.nonzero .d .r4) t = some (decide (6-j ≠ 0)) at he
    constructor
    · intro hl
      rw [he, show 6-j = 0 by omega]
      rfl
    · intro hl
      rw [he]
      simp only [ne_eq, show ¬6-j = 0 by omega, not_false_eq_true, decide_true]
  refine WP.seq (WP.mono (WP.chunk_loop (by decide) (by omega) h step test) fun t ⟨j, hj, he, ht'⟩ => ?_)
  have ht : VInv8 base P S 6 t := (show j = 6 by omega) ▸ ht'
  refine WP.mono (rotRound_ok .v1 .v2 t (by decide) (by decide) ht.cst ht.rcon
    (by rw [ht.out]; exact schedule_wr hc ht.keep (by omega))) fun u ⟨_, R, hR, o⟩ => ?_
  refine ⟨(ht.keep.trans o.keep).mono (by simp [keyGprs]), ?_⟩
  rw [o.mem, ht.out, show 32 * 6 + 32 = 4 * (8 * 6 + 8) by rfl]
  exact store_good ht.good (keyA_next ht.keyA ht.keyB hR o) (by decide)

/-! ## Setup -/

theorem loadKey_ok (d : VReg) (p : Reg) (s : State) (hp : p ≠ .r0) (h12 : s.gpr .r12 = 0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr p) 16) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.loadKey d p)) s fun t =>
      t.vpr d = s.mem.read (s.gpr p) 16 ∧ Local [] [d] s t := by
  have hr' : InRegions (s.rd ++ s.wr) (s.gpr p + s.gpr .r12) 16 := by rw [h12]; simpa using hr
  apply WP.of_runBlock
  rw [Impl.Aes.PPC64LE.Crypto.loadKey, runBlock_cons, exec_lxvd2x d p .r12 s hp hr', runStep_some, runBlock_cons,
    exec_sldoi8, runStep_some, runBlock_nil]
  simp only [vpr_writeV, ite_true, Option.some.injEq, exists_eq_left', sldoi8_self, swapDwords_involutive, h12]
  refine ⟨by simp, ((Local.writeV _ _ _).trans (Local.writeV _ _ _)).weaken (by simp) (by simp)⟩

theorem setCtl_ok (d : VReg) (x : BitVec 64) (s : State) (hd : d ≠ .v3 ∧ d ≠ .v4) (hz : s.vpr .v4 = 0) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.setCtl d x)) s fun t =>
      t.vpr d = x ++ x ∧ Local [.r8] [d, .v3] s t := by
  rw [Impl.Aes.PPC64LE.Crypto.setCtl, WP.block_append_iff]
  refine WP.mono (const64_ok .r8 x s) fun u hu => ?_
  subst hu
  refine WP.mono (pair_ok d .v3 .v4 .r8 .r8 _ hd.1 hd.2 (by decide) (by rw [vpr_write]; exact hz)) fun t ⟨ht, ho⟩ => ?_
  refine ⟨by rw [ht, RegUpd.gpr_write_self], ((Local.write _ _ _).trans (Local.of_vector ho)).weaken (by simp)
    (by simp)⟩

theorem gprs_ok (is : List Instr) (s t : State) (gs : List Reg) (h : runBlock isa is s = some t)
    (hl : Local gs [] s t) : WP isa (.block is) s fun u => u = t ∧ Local gs [] s u :=
  WP.of_runBlock ⟨t, h, rfl, hl⟩

/-- After the key is copied: the constants, and the key's first four (eight)
words in `v1` (`v2`). -/
structure VStart (base : State) (P S : Addr) (nk : Nat) (s : State) : Prop where
  keep : Keep keyGprs base s
  cst : VConst s
  out : s.gpr .r5 = S + BitVec.ofNat 64 (4 * nk)
  len : s.gpr .r7 = BitVec.ofNat 64 (4 * nk)
  rcon : s.gpr .r6 = (rc 1).setWidth 64
  keyA : Rk (W base.mem P nk) 0 (s.vpr .v1)
  keyB : nk = 8 → Rk (W base.mem P nk) 4 (s.vpr .v2)
  good : Good s.mem S (W base.mem P nk) nk
  frame : Frame [⟨S, 240⟩] base.mem s.mem

theorem vecSetup_ok {base s : State} {P S : Addr} {nk : Nat} (hc : KeyConfig base P S (4 * nk))
    (h3 : nk = 4 ∨ nk = 8) (hk : Keep keyGprs base s) (h5 : s.gpr .r5 = S + BitVec.ofNat 64 (4 * nk))
    (h7 : s.gpr .r7 = BitVec.ofNat 64 (4 * nk)) (hg : Good s.mem S (W base.mem P nk) nk)
    (hf : Frame [⟨S, 240⟩] base.mem s.mem) :
    WP isa (.block Impl.Aes.PPC64LE.Crypto.vecSetup) s (VStart base P S nk) := by
  have hS : InRegions (s.rd ++ s.wr) S 16 := by
    have e := Offset.contains_base S (d := 0) (n := 16) (k := 240) (by decide) (by decide)
    rw [BitVec.add_zero] at e
    rw [hk.2.1, hk.2.2]
    exact ⟨⟨S, 240⟩, List.mem_append_right _ hc.schedule, e⟩
  have hS16 : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 16) 16 := by
    rw [hk.2.1, hk.2.2]
    exact ⟨⟨S, 240⟩, List.mem_append_right _ hc.schedule, Offset.contains_base S (by decide) (by decide)⟩
  rw [Impl.Aes.PPC64LE.Crypto.vecSetup]
  iterate 8 rw [WP.block_append_iff]
  -- `r11 = S`, `r12 = 0`
  let s₁ := (s.write .r11 (s.gpr .r5 - s.gpr .r7)).write .r12 0#64
  have e₁ : s₁.gpr .r11 = S := by
    simp only [s₁, RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, h5, h7]
    exact BitVec.add_sub_cancel _ _
  refine WP.mono (gprs_ok _ s s₁ [.r11, .r12] (by
      simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, s₁, show (0 : Nat) < 2^15 by decide,
        ite_true])
    ((Local.write _ _ _).trans (Local.write _ _ _))) fun u₁ ⟨hu₁, l₁⟩ => ?_
  subst hu₁
  have r12₁ : s₁.gpr .r12 = 0 := by simp only [s₁, RegUpd.gpr_write_self]; rfl
  refine WP.mono (loadKey_ok .v1 .r11 s₁ (by decide) r12₁ (by rw [e₁, l₁.keep.2.1, l₁.keep.2.2]; exact hS))
    fun u₂ ⟨hv1, l₂⟩ => ?_
  let s₃ := u₂.write .r10 (u₂.gpr .r11 + BitVec.ofNat 64 16)
  refine WP.mono (gprs_ok _ u₂ s₃ [.r10] (by
      simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, s₃, show (16 : Nat) < 2^15 by decide,
        ne_eq, reduceCtorEq, not_false_eq_true, and_self, ite_true])
    (Local.write _ _ _)) fun u₃ ⟨hu₃, l₃⟩ => ?_
  subst hu₃
  have e₃ : s₃.gpr .r10 = S + BitVec.ofNat 64 16 := by
    simp only [s₃, RegUpd.gpr_write_self, l₂.keep.gpr (by simp), e₁]
  have l₁₃ := (l₁.trans l₂).trans l₃
  refine WP.mono (loadKey_ok .v2 .r10 s₃ (by decide) ((l₂.trans l₃).keep.gpr (by simp) |>.trans r12₁)
    (by rw [e₃, l₁₃.keep.2.1, l₁₃.keep.2.2]; exact hS16)) fun u₄ ⟨hv2, l₄⟩ => ?_
  refine WP.mono (vector_step (.vop (.logic .xor .v4 .v4 .v4)) .v4 _ u₄ rfl) fun u₅ ⟨hz, o₅⟩ => ?_
  rw [BitVec.xor_self] at hz
  refine WP.mono (setCtl_ok .v5 rotCtl u₅ (by decide) hz) fun u₆ ⟨h5', l₆⟩ => ?_
  refine WP.mono (setCtl_ok .v6 subCtl u₆ (by decide) ((l₆.v _ (by decide)).trans hz)) fun u₇ ⟨h6', l₇⟩ => ?_
  refine WP.mono (setCtl_ok .v7 rcCtl u₇ (by decide)
    ((l₇.v _ (by decide)).trans ((l₆.v _ (by decide)).trans hz))) fun u₈ ⟨h7', l₈⟩ => ?_
  refine WP.mono (gprs_ok _ u₈ (u₈.write .r6 (BitVec.ofNat 64 1)) [.r6] (by
      simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, show (1 : Nat) < 2^15 by decide,
        ite_true]) (Local.write _ _ _)) fun u ⟨hu, l₉⟩ => ?_
  subst hu
  have L := (((((((l₁.trans l₂).trans l₃).trans l₄).trans (Local.of_vector o₅)).trans l₆).trans l₇).trans l₈).trans l₉
  have hm : (u₈.write .r6 (BitVec.ofNat 64 1)).mem = s.mem := L.mem
  have hv1' : (u₈.write .r6 (BitVec.ofNat 64 1)).vpr .v1 = s.mem.read S 16 := by
    rw [l₉.v _ (by simp), l₈.v _ (by simp), l₇.v _ (by simp), l₆.v _ (by simp), o₅.v _ (by simp), l₄.v _ (by simp),
      l₃.v _ (by simp), hv1, e₁, l₁.mem]
  have hv2' : (u₈.write .r6 (BitVec.ofNat 64 1)).vpr .v2 = s.mem.read (S + BitVec.ofNat 64 16) 16 := by
    rw [l₉.v _ (by simp), l₈.v _ (by simp), l₇.v _ (by simp), l₆.v _ (by simp), o₅.v _ (by simp), hv2, e₃,
      (l₁.trans (l₂.trans l₃)).mem]
  refine ⟨(hk.trans L.keep).mono (by simp [keyGprs]), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [l₉.v _ (by simp), l₈.v _ (by simp), l₇.v _ (by simp), l₆.v _ (by simp)]; exact hz
  · rw [l₉.v _ (by simp), l₈.v _ (by simp), l₇.v _ (by simp)]; exact h5'
  · rw [l₉.v _ (by simp), l₈.v _ (by simp)]; exact h6'
  · rw [l₉.v _ (by simp)]; exact h7'
  · rw [l₉.keep.gpr (by simp), l₈.keep.gpr (by simp), l₇.keep.gpr (by simp), l₆.keep.gpr (by simp),
      (Local.of_vector o₅).keep.gpr (by simp), l₄.keep.gpr (by simp), l₃.keep.gpr (by simp), l₂.keep.gpr (by simp)]
    exact r12₁
  · rw [L.keep.gpr (by simp)]; exact h5
  · rw [L.keep.gpr (by simp)]; exact h7
  · rw [RegUpd.gpr_write_self]; rfl
  · rw [hv1']
    have e := load_rk (j := 0) hg (by omega) (by omega)
    rwa [Nat.mul_zero, BitVec.add_zero] at e
  · intro h8
    subst h8
    rw [hv2']
    exact load_rk (j := 4) hg (by omega) (by omega)
  · rw [hm]; exact hg
  · rw [hm]; exact hf

end VG.Proof.Aes.PPC64LE.Crypto
