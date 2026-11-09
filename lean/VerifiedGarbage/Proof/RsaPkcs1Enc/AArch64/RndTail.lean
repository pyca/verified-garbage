module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndInvoke
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the zero loops

The three loops that store zeros, `n` bytes from a pointer register
counting down a counter register (`zloop_ok`): the wipe of `PS`, `out`
zeroed and the octets drawn wiped.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random

/-- The body of a zero loop. -/
abbrev zbody (rz rp rc : Reg) : List Instr := [.strb rz rp 0, .addImm .x rp rp 1, .subImm .x rc rc 1]

/-- After one iteration, from `t`. -/
structure ZStep (rz rp rc : Reg) (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  mem : u.mem = t.mem.write (t.gpr rp) 1 ((t.gpr rz).setWidth 8)
  ptr : u.gpr rp = t.gpr rp + BitVec.ofNat 64 1
  ctr : u.gpr rc = t.gpr rc - BitVec.ofNat 64 1
  other : ∀ r, r ≠ rp → r ≠ rc → u.gpr r = t.gpr r

theorem zbody_ok {rz rp rc : Reg} (hpc : rp ≠ rc) {t : State}
    (hw : InRegions t.wr (t.gpr rp + BitVec.ofNat 64 0) 1) :
    WP isa (.block (zbody rz rp rc)) t (ZStep rz rp rc t) := by
  apply WP.of_runBlock
  simp only [zbody, runBlock_cons, runStep_some, runBlock_nil, reduceExec, addr, State.store,
    State.read, Size.bits, BitVec.setWidth_eq, Option.bind_some,
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, ite_true, 
    RegUpd.gpr_write, hw,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, fun r h1 h2 => ?_⟩
  · simp only [RegUpd.mem_write, BitVec.add_zero, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]
  · simp only [RegUpd.gpr_write, hpc, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, Ne.symm hpc, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [RegUpd.gpr_write, h1, h2, ite_false]

/-- After `k` of the `n` iterations of a zero loop from `t`. -/
structure ZInv (rp rc : Reg) (p : Addr) (n : Nat) (t : State) (k : Nat) (u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  v : u.v = t.v
  keep : Keeps [rp, rc] t u
  ptr : u.gpr rp = p + BitVec.ofNat 64 k
  ctr : u.gpr rc = BitVec.ofNat 64 (n - k)
  fr : Frame [⟨p, n⟩] t.mem u.mem
  zero : ∀ j < k, u.mem (p + BitVec.ofNat 64 j) = 0

theorem zloop_ok {rz rp rc : Reg} (hpc : rp ≠ rc) (hzp : rz ≠ rp) (hzc : rz ≠ rc) {p : Addr} {n : Nat}
    (hn : 0 < n) (hn' : n < 2 ^ 64) {t : State} (hR : ∃ R ∈ t.wr, Region.Sub ⟨p, n⟩ R)
    (hz : t.gpr rz = 0) (hp0 : t.gpr rp = p) (hc0 : t.gpr rc = BitVec.ofNat 64 n) :
    WP isa (.loop (.block (zbody rz rp rc)) (.nonzero .x rc)) t (ZInv rp rc p n t n) := by
  obtain ⟨R, hRm, hRs⟩ := hR
  refine Bytes.count_loop hn (ZInv rp rc p n t) (fun k hk u hu => ?_)
    ⟨rfl, rfl, rfl, rfl, Keeps.refl _ _, by rw [hp0, add_zero'], by rw [hc0, Nat.sub_zero],
      Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have hc : (⟨p, n⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  have hw : InRegions u.wr (u.gpr rp + BitVec.ofNat 64 0) 1 := by
    rw [add_zero', hu.ptr, hu.wr]; exact ⟨R, hRm, hRs _ hc⟩
  refine WP.mono (zbody_ok hpc hw) fun w hw' => ?_
  have hzu : u.gpr rz = 0 := (hu.keep rz (by simp [hzp, hzc])).trans hz
  have hm : w.mem = u.mem.write (p + BitVec.ofNat 64 k) 1 0 := by rw [hw'.mem, hu.ptr, hzu]; rfl
  have hrc : w.gpr rc = BitVec.ofNat 64 (n - (k + 1)) := by rw [hw'.ctr, hu.ctr, Bytes.counter_step hk hn']
  refine ⟨⟨hw'.rd.trans hu.rd, hw'.wr.trans hu.wr, hw'.sp.trans hu.sp, hw'.v.trans hu.v, fun r hr => ?_,
    by rw [hw'.ptr, hu.ptr, add_add'], hrc, by rw [hm]; exact hu.fr.write (List.mem_singleton_self _) _ hc,
    fun j hj => ?_⟩, by rw [hrc, Bytes.counter_ne hk hn']⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hw'.other r hr.1 hr.2]; exact hu.keep r (by simp [hr.1, hr.2])
  · rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Bytes.write1_ne _ _ (Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))]; exact hu.zero j hj
    · exact Bytes.write1_self _ _ _

/-- The zero loop's bytes. -/
theorem zloop_bytes {rp rc : Reg} {p : Addr} {n : Nat} {t u : State} (h : ZInv rp rc p n t n u) :
    Spec.Rsa.bytesAt u.mem p n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro j h₁ _
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact h.zero j h₁

/-- What every path leaves, at the end of the frames' body. -/
structure Fin (P : Nat) (s x : State) : Prop where
  sp : x.sp = Q s
  rd : x.rd = s.rd
  wr : x.wr = (entered s).wr
  fr : Frame [stkR P s, tapeR s, outR s, scrR s] s.mem x.mem
  lr : x.mem.readW (off (Q s) 1088) 64 = s.gpr .x30
  cs : ∀ r ∈ preserved, r ≠ .x30 → x.gpr r = s.gpr r
  vs : ∀ r ∈ preservedV, (x.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- After `status`, from `u`. -/
structure StatusStep (s u w : State) : Prop where
  rd : w.rd = u.rd
  wr : w.wr = u.wr
  sp : w.sp = u.sp
  vv : w.v = u.v
  mem : w.mem = u.mem
  x0 : (w.gpr .x0).setWidth 32 = 2 - (u.gpr .x0).setWidth 32
  x12 : w.gpr .x12 = BitVec.ofNat 64 1024
  x13 : w.gpr .x13 = off (Q s) oBuf
  x14 : w.gpr .x14 = 0
  keep : Keeps [.x0, .x9, .x12, .x13, .x14] u w

theorem status_ok {P : Nat} {s u : State} {i : Nat} {pad : List Byte} (h : AfterCall P s u i pad) :
    WP isa (.block status) u (StatusStep s u) := by
  have hsp := h.sp
  apply WP.of_runBlock
  simp only [status, oBuf, runBlock_cons, runStep_some, runBlock_nil, reduceExec, 
    State.read, Size.bits, BitVec.setWidth_eq, Nat.reduceLT, Nat.reduceMul,
    BitVec.shiftLeft_zero, ite_true, hsp, RegUpd.sp_write, RegUpd.gpr_write,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h9, h12, h13, h14⟩ := hr
    simp only [RegUpd.gpr_write, h0, h9, h12, h13, h14, ite_false]

theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun j hj => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hj)

theorem written_random {m : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {res : Option (List Byte)}
    (h : Spec.Rsa.written m out k r res) : Spec.RsaPkcs1Enc.writtenRandom m out k (2 - r) res := by
  cases res with
  | some C => obtain ⟨h1, h2⟩ := h; exact ⟨by rw [h1]; rfl, h2⟩
  | none => obtain ⟨h1, h2⟩ := h; exact ⟨by rw [h1]; rfl, h2⟩

/-- `PS`'s area in the frame. -/
abbrev psR (s : State) : Region := ⟨off (Q s) oBuf, 1024⟩

theorem psR_sub {P : Nat} (s : State) : Region.Sub (psR s) (stkR P s) :=
  frame_sub s (by unfold oBuf; omega)

/-- The status and the wipe of `PS`, after the call. -/
theorem accTail_ok {P : Nat} {s u : State} (hp : RPre P s) {i : Nat} {pad : List Byte}
    (h : AfterCall P s u i pad) :
    WP isa (.seq (.block status) wipe) u fun x => Fin P s x ∧
      x.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 i ∧ x.mem.readW (s.gpr .x2 + BitVec.ofNat 64 8) 64 = 0 ∧
      (Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
        Spec.RsaPkcs1Enc.writtenRandom x.mem (s.gpr .x0) (kOf s) ((x.gpr .x0).setWidth 32)
          (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) pad)) := by
  have hP := hp.ps
  have hQ := Q_toNat hp
  refine WP.seq (WP.mono (status_ok h) fun w hw => ?_)
  have hR : ∃ R ∈ w.wr, Region.Sub (psR s) R :=
    ⟨⟨Q s, frameBytes⟩, by rw [hw.wr, h.wr, entered_wr]; simp, Offset.sub_base _ (by unfold oBuf frameBytes; omega)⟩
  refine WP.mono (zloop_ok (rz := .x14) (rp := .x13) (rc := .x12) (by decide) (by decide) (by decide)
    (by decide) (by decide) hR hw.x14 hw.x13 hw.x12) fun x hx => ?_
  have hf : Frame [psR s] u.mem x.mem := by rw [← hw.mem]; exact hx.fr
  have dK : ∀ {R : Region}, (stkR P s).Disjoint R → ∀ r ∈ [psR s], R.Disjoint r := fun hd r hr => by
    rw [List.mem_singleton.mp hr]; exact (hd.sub_left (psR_sub s)).symm
  have kx : ∀ r, r ∉ [Reg.x0, .x9, .x12, .x13, .x14] → x.gpr r = u.gpr r := fun r hr =>
    (hx.keep r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact ⟨hr.2.2.2.1, hr.2.2.1⟩)).trans
      (hw.keep r hr)
  refine ⟨⟨hx.sp.trans (hw.sp.trans h.sp), hx.rd.trans (hw.rd.trans h.rd), hx.wr.trans (hw.wr.trans h.wr),
    h.fr.trans (hf.sub fun r hr => ⟨stkR P s, by simp, by rw [List.mem_singleton.mp hr]; exact psR_sub s⟩),
    ?_, fun r hr h30 => (kx r ?_).trans (h.cs r hr h30), fun r hr => by rw [hx.v, hw.vv]; exact h.vs r hr⟩,
    ?_, ?_, fun hq => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by unfold oBuf; omega)) (by omega) (by unfold oBuf; omega)) (by decide)]
    exact h.lr
  · revert hr h30; revert r; decide
  · have ht0 : (tapeR s).Contains (s.gpr .x2) 8 := by
      have := Offset.contains_base (s.gpr .x2) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
      rwa [add_zero'] at this
    rw [hf.readW (w := 64) ht0 (dK hp.dKt) (by decide)]
    exact h.tape0
  · rw [hf.readW (w := 64) (r := tapeR s) (Offset.contains_base _ (by decide) (by decide)) (dK hp.dKt) (by decide)]
    exact h.tape1
  · have e : (⟨s.gpr .x0, kOf s⟩ : Region) = outR s := by rw [outR, kOf, hp.hsi]
    have h0 : (x.gpr .x0).setWidth 32 = 2 - (u.gpr .x0).setWidth 32 := by
      rw [hx.keep .x0 (by decide)]; exact hw.x0
    have hb := bytes_frame (p := s.gpr .x0) (n := kOf s) hf (by rw [e]; exact dK hp.dKo)
      (by have := hp.k2; unfold kOf; omega)
    have hw0 := written_random (h.res hq)
    rw [h0]
    revert hw0
    cases Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) pad <;>
      simp only [Spec.RsaPkcs1Enc.writtenRandom, hb] <;> exact id

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
