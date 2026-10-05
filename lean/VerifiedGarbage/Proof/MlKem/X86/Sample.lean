import VerifiedGarbage.Proof.MlKem.X86.AddSub
import VerifiedGarbage.Proof.Sha3.X86.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.X86.Permute
import VerifiedGarbage.Impl.MlKem.X86.Basic
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.X86.Sample
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.X86.Top
import VerifiedGarbage.Proof.MlKem.X86.NttInv
import VerifiedGarbage.Proof.MlKem.X86.Mul
import VerifiedGarbage.Proof.MlKem.X86.Cbd
import VerifiedGarbage.Proof.MlKem.X86.Encode12
import VerifiedGarbage.Proof.MlKem.X86.Decode12

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Keccak`. -/
section

/-!
# ML-KEM on x86 (32-bit): calling the Keccak streaming functions

What a call of `vg_keccak_absorb`, `vg_keccak_pad` or `vg_keccak_squeeze`
(with their per-target contracts, `Proof/Sha3/X86/Permute.lean`) needs of the
state it is made from (`CallPre`), with the arguments in `eax`, `ecx`, `edx`,
`ebx`, (`ebp`,) `edi`, pushed in a frame of their own (`rs6`, `rs5`); and what
holds when it returns. Each call uses the 40 bytes below `esp`: its arguments
(24 bytes), the return address, and the 12 bytes the callee's own calls use.

The pieces `absorb_piece`, `pad_piece` and `squeeze_piece` (`Piece.lean`)
make the calls from a state satisfying `AbsorbAt`, `PadAt` or `SqueezeAt`,
whose pointers are functions of the entry state, public when the entry
states' pointers agree.
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86
open VG.Proof.Sha3.X86 (reg32 within)
open VG.Spec.Sha3 (stateAt Repr bytesAt rates squeezeFrom absorb pad)

/-- The registers of the arguments of a call with six. -/
abbrev rs6 : List Reg := [.edi, .ebp, .ebx, .edx, .ecx, .eax]

/-- The registers of the arguments of a call with five. -/
abbrev rs5 : List Reg := [.edi, .ebx, .edx, .ecx, .eax]

theorem absorb_nosp : NoSp Impl.Sha3.X86.Stream.absorb := NoSp.of_all (by decide +kernel)
theorem pad_nosp : NoSp Impl.Sha3.X86.Stream.pad := NoSp.of_all (by decide +kernel)
theorem squeeze_nosp : NoSp Impl.Sha3.X86.Stream.squeeze := NoSp.of_all (by decide +kernel)

theorem absorb_stack : stackUse Impl.Sha3.X86.Stream.absorb = 12 := by decide +kernel
theorem pad_stack : stackUse Impl.Sha3.X86.Stream.pad = 12 := by decide +kernel
theorem squeeze_stack : stackUse Impl.Sha3.X86.Stream.squeeze = 12 := by decide +kernel

/-- The stack a call uses, below `E`: its arguments' frame, its return
address and the 12 bytes below it. -/
theorem stack_parts {E : BitVec 32} (hE : 40 ≤ E.toNat) :
    Region.Sub (below E 24) (below E 40) ∧
      Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below E 40) ∧
      Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64 - 12, 12⟩ (below E 40) ∧
      Region.Sub (below E 20) (below E 40) ∧
      Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below E 40) ∧
      Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64 - 12, 12⟩ (below E 40) := by
  have r1 : ∀ k, k + 4 ≤ 40 → Region.Sub ⟨(E - BitVec.ofNat 32 (k + 4)).setWidth 64, 4⟩ (below E 40) :=
    fun k hk => by
      have := below_inner (sp := E) (a := 4) (b := 40) (k := k) (by omega) hE
      have e : (⟨(E - BitVec.ofNat 32 (k + 4)).setWidth 64, 4⟩ : Region) = below (E - BitVec.ofNat 32 k) 4 := by
        simp only [below]; congr 2; bv_omega
      rw [e]; exact this
  have r2 : ∀ k, k + 12 ≤ 40 → Region.Sub ⟨(E - BitVec.ofNat 32 k).setWidth 64 - 12, 12⟩ (below E 40) :=
    fun k hk => by
      have := below_inner (sp := E) (a := 12) (b := 40) (k := k) (by omega) hE
      have e : (⟨(E - BitVec.ofNat 32 k).setWidth 64 - 12, 12⟩ : Region) = below (E - BitVec.ofNat 32 k) 12 := by
        simp only [below]
        rw [Taint.sub_setWidth (show 12 ≤ (E - BitVec.ofNat 32 k).toNat by rw [sub_toNat (by omega)]; omega)]
        rfl
      rw [e]; exact this
  exact ⟨below_sub (by omega) hE, r1 24 (by omega), r2 28 (by omega), below_sub (by omega) hE, r1 20 (by omega),
    r2 24 (by omega)⟩

/-- Where the state `S` and working space `W` of a Keccak call are, with `esp = E`. -/
structure KBufs (E S W : BitVec 32) : Prop where
  hE : 40 ≤ E.toNat
  fS : S.toNat + 200 ≤ 2 ^ 32
  fW : W.toNat + 640 ≤ 2 ^ 32
  dSW : (reg32 S 200).Disjoint (reg32 W 640)
  bS : (below E 40).Disjoint (reg32 S 200)
  bW : (below E 40).Disjoint (reg32 W 640)

/-- A region within one of `rs`. -/
def Within (r : Region) (rs : List Region) : Prop :=
  ∃ r' ∈ rs, ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len

theorem entry_frame {s : State} {E : BitVec 32} (hesp : s.gpr .esp = E) (hE : 40 ≤ E.toNat) {rs : List Reg}
    (hrs : Reg.esp ∉ rs) (hl : rs.length ≤ 6) :
    Frame [below E 40] s.mem (pushed rs s).callEntry.mem :=
  (callEntry_frame (by rw [hesp]; omega) hrs).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [hesp]; exact below_sub (by omega) hE⟩

/-! ## `vg_keccak_absorb` -/

/-- `absorb(S, rate, pos, D, len, W)`'s arguments. -/
structure AbsArgs (s : State) (S D W : BitVec 32) (rate pos len : Nat) : Prop where
  eax : s.gpr .eax = S
  ecx : s.gpr .ecx = BitVec.ofNat 32 rate
  edx : s.gpr .edx = BitVec.ofNat 32 pos
  ebx : s.gpr .ebx = D
  ebp : s.gpr .ebp = BitVec.ofNat 32 len
  edi : s.gpr .edi = W

theorem absorb_pre {s : State} {E S D W : BitVec 32} {rate pos len : Nat} (hesp : s.gpr .esp = E)
    (ha : VG.Proof.MlKem.X86.AbsArgs s S D W rate pos len) (hk : VG.Proof.MlKem.X86.KBufs E S W) (fD : D.toNat + len ≤ 2 ^ 32)
    (dDS : (reg32 D len).Disjoint (reg32 S 200)) (dDW : (reg32 D len).Disjoint (reg32 W 640))
    (bD : (below E 40).Disjoint (reg32 D len)) (hr : rate ∈ rates) (hp : pos < rate) (hlen : len < 2 ^ 32)
    (cD : VG.Proof.MlKem.X86.Within (reg32 D len) (s.rd ++ s.wr)) (cS : VG.Proof.MlKem.X86.Within (reg32 S 200) s.wr)
    (cW : VG.Proof.MlKem.X86.Within (reg32 W 640) s.wr) :
    CallPre Proof.Sha3.absorbX86 VG.Proof.MlKem.X86.rs6 [reg32 D len] [reg32 S 200, reg32 W 640, below E 24] s := by
  have hE := hk.hE
  have fit : 4 * rs6.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrate : rate < 2 ^ 32 := by simp [rates] at hr; omega
  have a0 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 0 = S := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.eax
  have a1 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 1 = BitVec.ofNat 32 rate := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a3 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 3 = D := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebx
  have a4 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 4 = BitVec.ofNat 32 len := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebp
  have a5 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 5 = W := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edi
  have eA : argAddr (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 0 = (E - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0, hesp]; rfl
  have eSp : (pushed VG.Proof.MlKem.X86.rs6 s).callEntry.gpr .esp = E - BitVec.ofNat 32 28 := by rw [callEntry_esp', hesp]; rfl
  have t1 : (BitVec.ofNat 32 rate).toNat = rate := toNat_ofNat32 hrate
  have t2 : (BitVec.ofNat 32 pos).toNat = pos := toNat_ofNat32 (by omega)
  have t4 : (BitVec.ofNat 32 len).toNat = len := toNat_ofNat32 hlen
  obtain ⟨p24, pr, pst, -, -, -⟩ := VG.Proof.MlKem.X86.stack_parts hE
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Sha3.absorbX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, t1, t2, t4]
    refine ⟨trivial, trivial, hk.dSW, dDS, dDW, hk.bS.sub_left p24, bD.sub_left p24, hk.bW.sub_left p24,
      hk.bS.sub_left pr, bD.sub_left pr, hk.bW.sub_left pr, hk.bS.sub_left pst, bD.sub_left pst,
      hk.bW.sub_left pst, hk.fS, fD, hk.fW, by rw [sub_toNat (by omega)]; omega,
      by rw [sub_toNat (by omega)]; have := E.isLt; omega, hr, hp⟩
  · refine Covers.of_sub fun r hr' => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr'', o, hb, hl⟩ := cD
      refine ⟨r', ?_, o, hb, hl⟩
      rcases List.mem_append.mp hr'' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    · obtain ⟨r', hr'', o, hb, hl⟩ := cS
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cW
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · exact VG.Proof.Sha3.X86.within (below (s.gpr .esp) (4 * rs6.length)) (by simp) 0 (by rw [hesp]; simp) (by simp)
  · refine Covers.of_sub fun r hr' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · obtain ⟨r', hr'', o, hb, hl⟩ := cS
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cW
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · exact VG.Proof.Sha3.X86.within (below (s.gpr .esp) (4 * rs6.length)) (by simp) 0 (by rw [hesp]; simp) (by simp)

theorem absorb_post {s s' : State} {E S D W : BitVec 32} {rate pos len : Nat} (hesp : s.gpr .esp = E)
    (ha : VG.Proof.MlKem.X86.AbsArgs s S D W rate pos len) (hE : 40 ≤ E.toNat) (hlen : len < 2 ^ 32) (hrate : rate < 2 ^ 32)
    (hpos : pos < 2 ^ 32) (bS : (below E 40).Disjoint (reg32 S 200)) (bD : (below E 40).Disjoint (reg32 D len))
    {rd wr : List Region}
    (h : ∃ s₂ : State, s₂.mem = s'.mem ∧
      Proof.Sha3.absorbX86.post ((pushed VG.Proof.MlKem.X86.rs6 s).callEntry.withRegions rd wr) s₂) :
    ∀ msg, Repr s.mem (S.setWidth 64) rate msg → pos = msg.length % rate →
      Repr s'.mem (S.setWidth 64) rate (msg ++ bytesAt s.mem (D.setWidth 64) len) := by
  obtain ⟨s₂, m₂, post, -⟩ := h
  have fit : 4 * rs6.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have a0 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 0 = S := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.eax
  have a1 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 1 = BitVec.ofNat 32 rate := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a3 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 3 = D := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebx
  have a4 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 4 = BitVec.ofNat 32 len := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebp
  have fr := VG.Proof.MlKem.X86.entry_frame hesp hE (rs := VG.Proof.MlKem.X86.rs6) (by decide) (by decide)
  simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, toNat_ofNat32 hlen,
    toNat_ofNat32 hrate, toNat_ofNat32 hpos, m₂] at post
  intro msg hm hp
  have eS : stateAt (pushed VG.Proof.MlKem.X86.rs6 s).callEntry.mem (S.setWidth 64) = stateAt s.mem (S.setWidth 64) :=
    Proof.Sha3.stateAt_congr fun i hi => fr.bytes (R := reg32 S 200) (by simpa using bS.symm) (by simp) hi
  have eD : bytesAt (pushed VG.Proof.MlKem.X86.rs6 s).callEntry.mem (D.setWidth 64) len = bytesAt s.mem (D.setWidth 64) len :=
    bytesAt_frame fr (by simpa using bD.symm) (by omega)
  have := post msg (by unfold Spec.Sha3.Repr; rw [eS]; exact hm) hp
  rwa [eD] at this

/-! ## `vg_keccak_pad` -/

/-- `pad(S, rate, pos, suffix, W)`'s arguments. -/
structure PadArgs (s : State) (S W : BitVec 32) (rate pos sfx : Nat) : Prop where
  eax : s.gpr .eax = S
  ecx : s.gpr .ecx = BitVec.ofNat 32 rate
  edx : s.gpr .edx = BitVec.ofNat 32 pos
  ebx : s.gpr .ebx = BitVec.ofNat 32 sfx
  edi : s.gpr .edi = W

theorem pad_pre {s : State} {E S W : BitVec 32} {rate pos sfx : Nat} (hesp : s.gpr .esp = E)
    (ha : VG.Proof.MlKem.X86.PadArgs s S W rate pos sfx) (hk : VG.Proof.MlKem.X86.KBufs E S W) (hr : rate ∈ rates) (hp : pos < rate)
    (cS : VG.Proof.MlKem.X86.Within (reg32 S 200) s.wr) (cW : VG.Proof.MlKem.X86.Within (reg32 W 640) s.wr) :
    CallPre Proof.Sha3.padX86 VG.Proof.MlKem.X86.rs5 [] [reg32 S 200, reg32 W 640, below E 20] s := by
  have hE := hk.hE
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrate : rate < 2 ^ 32 := by simp [rates] at hr; omega
  have a0 : arg (pushed VG.Proof.MlKem.X86.rs5 s).callEntry 0 = S := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.eax
  have a1 : arg (pushed VG.Proof.MlKem.X86.rs5 s).callEntry 1 = BitVec.ofNat 32 rate := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed VG.Proof.MlKem.X86.rs5 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a4 : arg (pushed VG.Proof.MlKem.X86.rs5 s).callEntry 4 = W := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edi
  have eA : argAddr (pushed VG.Proof.MlKem.X86.rs5 s).callEntry 0 = (E - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0, hesp]; rfl
  have eSp : (pushed VG.Proof.MlKem.X86.rs5 s).callEntry.gpr .esp = E - BitVec.ofNat 32 24 := by rw [callEntry_esp', hesp]; rfl
  have t1 : (BitVec.ofNat 32 rate).toNat = rate := toNat_ofNat32 hrate
  have t2 : (BitVec.ofNat 32 pos).toNat = pos := toNat_ofNat32 (by omega)
  obtain ⟨-, -, -, p20, pr, pst⟩ := VG.Proof.MlKem.X86.stack_parts hE
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Sha3.padX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a4, eA, eSp, t1, t2]
    refine ⟨trivial, trivial, hk.dSW, hk.bS.sub_left p20, hk.bW.sub_left p20, hk.bS.sub_left pr,
      hk.bW.sub_left pr, hk.bS.sub_left pst, hk.bW.sub_left pst, hk.fS, hk.fW,
      by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := E.isLt; omega, hr, hp⟩
  · refine Covers.of_sub fun r hr' => ?_
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · obtain ⟨r', hr'', o, hb, hl⟩ := cS
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cW
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · exact VG.Proof.Sha3.X86.within (below (s.gpr .esp) (4 * rs5.length)) (by simp) 0 (by rw [hesp]; simp) (by simp)
  · refine Covers.of_sub fun r hr' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · obtain ⟨r', hr'', o, hb, hl⟩ := cS
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cW
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · exact VG.Proof.Sha3.X86.within (below (s.gpr .esp) (4 * rs5.length)) (by simp) 0 (by rw [hesp]; simp) (by simp)

theorem pad_post {s s' : State} {E S W : BitVec 32} {rate pos sfx : Nat} (hesp : s.gpr .esp = E)
    (ha : VG.Proof.MlKem.X86.PadArgs s S W rate pos sfx) (hE : 40 ≤ E.toNat) (hrate : rate < 2 ^ 32) (hpos : pos < 2 ^ 32)
    (bS : (below E 40).Disjoint (reg32 S 200)) {rd wr : List Region}
    (h : ∃ s₂ : State, s₂.mem = s'.mem ∧
      Proof.Sha3.padX86.post ((pushed VG.Proof.MlKem.X86.rs5 s).callEntry.withRegions rd wr) s₂) :
    ∀ msg, Repr s.mem (S.setWidth 64) rate msg → pos = msg.length % rate →
      stateAt s'.mem (S.setWidth 64) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg) := by
  obtain ⟨s₂, m₂, post⟩ := h
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have a0 : arg (pushed VG.Proof.MlKem.X86.rs5 s).callEntry 0 = S := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.eax
  have a1 : arg (pushed VG.Proof.MlKem.X86.rs5 s).callEntry 1 = BitVec.ofNat 32 rate := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed VG.Proof.MlKem.X86.rs5 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a3 : arg (pushed VG.Proof.MlKem.X86.rs5 s).callEntry 3 = BitVec.ofNat 32 sfx := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebx
  have fr := VG.Proof.MlKem.X86.entry_frame hesp hE (rs := VG.Proof.MlKem.X86.rs5) (by decide) (by decide)
  simp only [Proof.Sha3.padX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, toNat_ofNat32 hrate,
    toNat_ofNat32 hpos, m₂] at post
  intro msg hm hp
  have eS : stateAt (pushed VG.Proof.MlKem.X86.rs5 s).callEntry.mem (S.setWidth 64) = stateAt s.mem (S.setWidth 64) :=
    Proof.Sha3.stateAt_congr fun i hi => fr.bytes (R := reg32 S 200) (by simpa using bS.symm) (by simp) hi
  exact post msg (by unfold Spec.Sha3.Repr; rw [eS]; exact hm) hp

/-! ## `vg_keccak_squeeze` -/

theorem squeeze_pre {s : State} {E S O W : BitVec 32} {rate pos len : Nat} (hesp : s.gpr .esp = E)
    (ha : VG.Proof.MlKem.X86.AbsArgs s S O W rate pos len) (hk : VG.Proof.MlKem.X86.KBufs E S W) (fO : O.toNat + len ≤ 2 ^ 32)
    (dSO : (reg32 S 200).Disjoint (reg32 O len)) (dOW : (reg32 O len).Disjoint (reg32 W 640))
    (bO : (below E 40).Disjoint (reg32 O len)) (hr : rate ∈ rates) (hp : pos ≤ rate) (hlen : len < 2 ^ 32)
    (cS : VG.Proof.MlKem.X86.Within (reg32 S 200) s.wr) (cO : VG.Proof.MlKem.X86.Within (reg32 O len) s.wr) (cW : VG.Proof.MlKem.X86.Within (reg32 W 640) s.wr) :
    CallPre Proof.Sha3.squeezeX86 VG.Proof.MlKem.X86.rs6 [] [reg32 S 200, reg32 O len, reg32 W 640, below E 24] s := by
  have hE := hk.hE
  have fit : 4 * rs6.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrate : rate < 2 ^ 32 := by simp [rates] at hr; omega
  have a0 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 0 = S := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.eax
  have a1 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 1 = BitVec.ofNat 32 rate := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a3 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 3 = O := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebx
  have a4 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 4 = BitVec.ofNat 32 len := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebp
  have a5 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 5 = W := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edi
  have eA : argAddr (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 0 = (E - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0, hesp]; rfl
  have eSp : (pushed VG.Proof.MlKem.X86.rs6 s).callEntry.gpr .esp = E - BitVec.ofNat 32 28 := by rw [callEntry_esp', hesp]; rfl
  have t1 : (BitVec.ofNat 32 rate).toNat = rate := toNat_ofNat32 hrate
  have t2 : (BitVec.ofNat 32 pos).toNat = pos := toNat_ofNat32 (by omega)
  have t4 : (BitVec.ofNat 32 len).toNat = len := toNat_ofNat32 hlen
  obtain ⟨p24, pr, pst, -, -, -⟩ := VG.Proof.MlKem.X86.stack_parts hE
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Sha3.squeezeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, t1, t2, t4]
    refine ⟨trivial, trivial, dSO, hk.dSW, dOW, hk.bS.sub_left p24, bO.sub_left p24, hk.bW.sub_left p24,
      hk.bS.sub_left pr, bO.sub_left pr, hk.bW.sub_left pr, hk.bS.sub_left pst, bO.sub_left pst,
      hk.bW.sub_left pst, hk.fS, fO, hk.fW, by rw [sub_toNat (by omega)]; omega,
      by rw [sub_toNat (by omega)]; have := E.isLt; omega, hr, hp⟩
  · refine Covers.of_sub fun r hr' => ?_
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr'', o, hb, hl⟩ := cS
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cO
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cW
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), o, hb, hl⟩
    · exact VG.Proof.Sha3.X86.within (below (s.gpr .esp) (4 * rs6.length)) (by simp) 0 (by rw [hesp]; simp) (by simp)
  · refine Covers.of_sub fun r hr' => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr'', o, hb, hl⟩ := cS
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cO
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · obtain ⟨r', hr'', o, hb, hl⟩ := cW
      exact ⟨r', List.mem_cons_of_mem _ hr'', o, hb, hl⟩
    · exact VG.Proof.Sha3.X86.within (below (s.gpr .esp) (4 * rs6.length)) (by simp) 0 (by rw [hesp]; simp) (by simp)

theorem squeeze_post {s s' : State} {E S O W : BitVec 32} {rate pos len : Nat} (hesp : s.gpr .esp = E)
    (ha : VG.Proof.MlKem.X86.AbsArgs s S O W rate pos len) (hE : 40 ≤ E.toNat) (hlen : len < 2 ^ 32) (hrate : rate < 2 ^ 32)
    (hpos : pos < 2 ^ 32) (bS : (below E 40).Disjoint (reg32 S 200)) {rd wr : List Region}
    (h : ∃ s₂ : State, s₂.mem = s'.mem ∧
      Proof.Sha3.squeezeX86.post ((pushed VG.Proof.MlKem.X86.rs6 s).callEntry.withRegions rd wr) s₂) :
    bytesAt s'.mem (O.setWidth 64) len = squeezeFrom rate (stateAt s.mem (S.setWidth 64)) pos len ∧
      ∃ pos' ≤ rate, ∀ d, squeezeFrom rate (stateAt s'.mem (S.setWidth 64)) pos' d =
        squeezeFrom rate (stateAt s.mem (S.setWidth 64)) (pos + len) d := by
  obtain ⟨s₂, m₂, post⟩ := h
  have fit : 4 * rs6.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have a0 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 0 = S := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.eax
  have a1 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 1 = BitVec.ofNat 32 rate := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ecx
  have a2 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 2 = BitVec.ofNat 32 pos := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.edx
  have a3 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 3 = O := by rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebx
  have a4 : arg (pushed VG.Proof.MlKem.X86.rs6 s).callEntry 4 = BitVec.ofNat 32 len := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact ha.ebp
  have fr := VG.Proof.MlKem.X86.entry_frame hesp hE (rs := VG.Proof.MlKem.X86.rs6) (by decide) (by decide)
  simp only [Proof.Sha3.squeezeX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4,
    toNat_ofNat32 hlen, toNat_ofNat32 hrate, toNat_ofNat32 hpos, m₂] at post
  have eS : stateAt (pushed VG.Proof.MlKem.X86.rs6 s).callEntry.mem (S.setWidth 64) = stateAt s.mem (S.setWidth 64) :=
    Proof.Sha3.stateAt_congr fun i hi => fr.bytes (R := reg32 S 200) (by simpa using bS.symm) (by simp) hi
  rw [eS] at post
  exact ⟨post.1, _, post.2.1, post.2.2⟩

/-! ## The calls, as pieces -/

theorem rate_lt {rate : Nat} (hr : rate ∈ rates) : rate < 2 ^ 32 := by simp [rates] at hr; omega

/-- Everything a call of `vg_keccak_absorb` needs of the state it is made from. -/
structure AbsorbAt (s : State) (E S D W : BitVec 32) (rate pos len : Nat) : Prop where
  esp : s.gpr .esp = E
  args : VG.Proof.MlKem.X86.AbsArgs s S D W rate pos len
  bufs : VG.Proof.MlKem.X86.KBufs E S W
  fD : D.toNat + len ≤ 2 ^ 32
  dDS : (reg32 D len).Disjoint (reg32 S 200)
  dDW : (reg32 D len).Disjoint (reg32 W 640)
  bD : (below E 40).Disjoint (reg32 D len)
  cD : VG.Proof.MlKem.X86.Within (reg32 D len) (s.rd ++ s.wr)
  cS : VG.Proof.MlKem.X86.Within (reg32 S 200) s.wr
  cW : VG.Proof.MlKem.X86.Within (reg32 W 640) s.wr

/-- Everything a call of `vg_keccak_pad` needs of the state it is made from. -/
structure PadAt (s : State) (E S W : BitVec 32) (rate pos sfx : Nat) : Prop where
  esp : s.gpr .esp = E
  args : VG.Proof.MlKem.X86.PadArgs s S W rate pos sfx
  bufs : VG.Proof.MlKem.X86.KBufs E S W
  cS : VG.Proof.MlKem.X86.Within (reg32 S 200) s.wr
  cW : VG.Proof.MlKem.X86.Within (reg32 W 640) s.wr

/-- Everything a call of `vg_keccak_squeeze` needs of the state it is made from. -/
structure SqueezeAt (s : State) (E S O W : BitVec 32) (rate pos len : Nat) : Prop where
  esp : s.gpr .esp = E
  args : VG.Proof.MlKem.X86.AbsArgs s S O W rate pos len
  bufs : VG.Proof.MlKem.X86.KBufs E S W
  fO : O.toNat + len ≤ 2 ^ 32
  dSO : (reg32 S 200).Disjoint (reg32 O len)
  dOW : (reg32 O len).Disjoint (reg32 W 640)
  bO : (below E 40).Disjoint (reg32 O len)
  cS : VG.Proof.MlKem.X86.Within (reg32 S 200) s.wr
  cO : VG.Proof.MlKem.X86.Within (reg32 O len) s.wr
  cW : VG.Proof.MlKem.X86.Within (reg32 W 640) s.wr

/-- Two runs that push the same six registers pass the same arguments. -/
theorem args6_eq {s s' : State} (hE : 40 ≤ (s.gpr .esp).toNat) (hsp : s.gpr .esp = s'.gpr .esp)
    (hr : ∀ r ∈ VG.Proof.MlKem.X86.rs6, s.gpr r = s'.gpr r) (rd wr : List Region) :
    ((pushed VG.Proof.MlKem.X86.rs6 s).callEntry.withRegions rd wr).gpr .esp = ((pushed VG.Proof.MlKem.X86.rs6 s').callEntry.withRegions rd wr).gpr .esp ∧
      ∀ i < 6, arg ((pushed VG.Proof.MlKem.X86.rs6 s).callEntry.withRegions rd wr) i =
        arg ((pushed VG.Proof.MlKem.X86.rs6 s').callEntry.withRegions rd wr) i := by
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', hsp], fun i hi => ?_⟩
  simp only [arg_withRegions]
  exact callEntry_arg_eq (by decide) (by simp only [List.length_cons, List.length_nil]; omega) hsp hr
    (by simpa using hi)

/-- Two runs that push the same five registers pass the same arguments. -/
theorem args5_eq {s s' : State} (hE : 40 ≤ (s.gpr .esp).toNat) (hsp : s.gpr .esp = s'.gpr .esp)
    (hr : ∀ r ∈ VG.Proof.MlKem.X86.rs5, s.gpr r = s'.gpr r) (rd wr : List Region) :
    ((pushed VG.Proof.MlKem.X86.rs5 s).callEntry.withRegions rd wr).gpr .esp = ((pushed VG.Proof.MlKem.X86.rs5 s').callEntry.withRegions rd wr).gpr .esp ∧
      ∀ i < 5, arg ((pushed VG.Proof.MlKem.X86.rs5 s).callEntry.withRegions rd wr) i =
        arg ((pushed VG.Proof.MlKem.X86.rs5 s').callEntry.withRegions rd wr) i := by
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', hsp], fun i hi => ?_⟩
  simp only [arg_withRegions]
  exact callEntry_arg_eq (by decide) (by simp only [List.length_cons, List.length_nil]; omega) hsp hr
    (by simpa using hi)

theorem absArgs_eq {s s' : State} {S D W : BitVec 32} {rate pos len : Nat} (h : VG.Proof.MlKem.X86.AbsArgs s S D W rate pos len)
    (h' : VG.Proof.MlKem.X86.AbsArgs s' S D W rate pos len) : ∀ r ∈ VG.Proof.MlKem.X86.rs6, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [VG.Proof.MlKem.X86.rs6, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.edi, h'.edi]
  · rw [h.ebp, h'.ebp]
  · rw [h.ebx, h'.ebx]
  · rw [h.edx, h'.edx]
  · rw [h.ecx, h'.ecx]
  · rw [h.eax, h'.eax]

theorem padArgs_eq {s s' : State} {S W : BitVec 32} {rate pos sfx : Nat} (h : VG.Proof.MlKem.X86.PadArgs s S W rate pos sfx)
    (h' : VG.Proof.MlKem.X86.PadArgs s' S W rate pos sfx) : ∀ r ∈ VG.Proof.MlKem.X86.rs5, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [VG.Proof.MlKem.X86.rs5, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.edi, h'.edi]
  · rw [h.ebx, h'.ebx]
  · rw [h.edx, h'.edx]
  · rw [h.ecx, h'.ecx]
  · rw [h.eax, h'.eax]

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {A B : State → State → Prop}

/-- A call of `vg_keccak_absorb`. -/
theorem absorb_piece (E S D W : State → BitVec 32) (rate pos len : Nat) (hr : rate ∈ rates) (hp : pos < rate)
    (hlen : len < 2 ^ 32) (hA : ∀ s₀ s, Pre s₀ → A s₀ s → VG.Proof.MlKem.X86.AbsorbAt s (E s₀) (S s₀) (D s₀) (W s₀) rate pos len)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
      E s₀ = E s₀' ∧ S s₀ = S s₀' ∧ D s₀ = D s₀' ∧ W s₀ = W s₀')
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 40] s.mem s'.mem →
      (∀ msg, Repr s.mem ((S s₀).setWidth 64) rate msg → pos = msg.length % rate →
        Repr s'.mem ((S s₀).setWidth 64) rate (msg ++ bytesAt s.mem ((D s₀).setWidth 64) len)) → B s₀ s') :
    Piece Pre Pub A B (Impl.MlKem.X86.callWith VG.Proof.MlKem.X86.rs6 "vg_keccak_absorb_scratch" Impl.Sha3.X86.Stream.absorb) := by
  refine Piece.callWith Proof.Sha3.X86.Stream.Absorb.absorb_verified.1
    Proof.Sha3.X86.Stream.Absorb.absorb_verified.2.1 VG.Proof.MlKem.X86.absorb_nosp (by decide) (by decide)
    (fun s₀ => [reg32 (D s₀) len]) (fun s₀ => [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 24])
    (fun s₀ s h₀ ha => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ha ha' => ?_)
    (fun s₀ s s' h₀ ha e₁ e₂ e₃ fr post => ?_)
  · have h := hA s₀ s h₀ ha
    have := h.bufs.hE
    rw [VG.Proof.MlKem.X86.absorb_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega
  · have h := hA s₀ s h₀ ha
    exact VG.Proof.MlKem.X86.absorb_pre h.esp h.args h.bufs h.fD h.dDS h.dDW h.bD hr hp hlen h.cD h.cS h.cW
  · obtain ⟨e₁, e₂, e₃, e₄⟩ := hpub s₀ s₀' h₀ h₀' hq
    have h := hA s₀ s h₀ ha
    have h' := hA s₀' s' h₀' ha'
    rw [← e₁, ← e₂, ← e₃, ← e₄] at h'
    have hsp : s.gpr .esp = s'.gpr .esp := h.esp.trans h'.esp.symm
    exact ⟨by rw [e₃], by rw [e₁, e₂, e₄], hsp,
      VG.Proof.MlKem.X86.args6_eq (by rw [h.esp]; exact h.bufs.hE) hsp (VG.Proof.MlKem.X86.absArgs_eq h.args h'.args) _ _⟩
  · have h := hA s₀ s h₀ ha
    have hE := h.bufs.hE
    refine hQ s₀ s s' h₀ ha e₁ e₂ e₃ (fr.sub fun r hr' => ?_)
      (VG.Proof.MlKem.X86.absorb_post h.esp h.args hE hlen (VG.Proof.MlKem.X86.rate_lt hr) (by have := VG.Proof.MlKem.X86.rate_lt hr; omega) h.bufs.bS h.bD post)
    rw [VG.Proof.MlKem.X86.absorb_stack, h.esp] at hr'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, below_sub (by omega) hE⟩
    · exact ⟨_, by simp, below_sub (by simp) hE⟩

/-- A call of `vg_keccak_pad`. -/
theorem pad_piece (E S W : State → BitVec 32) (rate pos sfx : Nat) (hr : rate ∈ rates) (hp : pos < rate)
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → VG.Proof.MlKem.X86.PadAt s (E s₀) (S s₀) (W s₀) rate pos sfx)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E s₀ = E s₀' ∧ S s₀ = S s₀' ∧ W s₀ = W s₀')
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 40] s.mem s'.mem →
      (∀ msg, Repr s.mem ((S s₀).setWidth 64) rate msg → pos = msg.length % rate →
        stateAt s'.mem ((S s₀).setWidth 64) = absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg)) →
      B s₀ s') :
    Piece Pre Pub A B (Impl.MlKem.X86.callWith VG.Proof.MlKem.X86.rs5 "vg_keccak_pad_scratch" Impl.Sha3.X86.Stream.pad) := by
  refine Piece.callWith Proof.Sha3.X86.Stream.Pad.pad_verified.1
    Proof.Sha3.X86.Stream.Pad.pad_verified.2.1 VG.Proof.MlKem.X86.pad_nosp (by decide) (by decide)
    (fun _ => []) (fun s₀ => [reg32 (S s₀) 200, reg32 (W s₀) 640, below (E s₀) 20])
    (fun s₀ s h₀ ha => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ha ha' => ?_)
    (fun s₀ s s' h₀ ha e₁ e₂ e₃ fr post => ?_)
  · have h := hA s₀ s h₀ ha
    have := h.bufs.hE
    rw [VG.Proof.MlKem.X86.pad_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega
  · have h := hA s₀ s h₀ ha
    exact VG.Proof.MlKem.X86.pad_pre h.esp h.args h.bufs hr hp h.cS h.cW
  · obtain ⟨e₁, e₂, e₃⟩ := hpub s₀ s₀' h₀ h₀' hq
    have h := hA s₀ s h₀ ha
    have h' := hA s₀' s' h₀' ha'
    rw [← e₁, ← e₂, ← e₃] at h'
    have hsp : s.gpr .esp = s'.gpr .esp := h.esp.trans h'.esp.symm
    exact ⟨rfl, by rw [e₁, e₂, e₃], hsp,
      VG.Proof.MlKem.X86.args5_eq (by rw [h.esp]; exact h.bufs.hE) hsp (VG.Proof.MlKem.X86.padArgs_eq h.args h'.args) _ _⟩
  · have h := hA s₀ s h₀ ha
    have hE := h.bufs.hE
    refine hQ s₀ s s' h₀ ha e₁ e₂ e₃ (fr.sub fun r hr' => ?_)
      (VG.Proof.MlKem.X86.pad_post h.esp h.args hE (VG.Proof.MlKem.X86.rate_lt hr) (by have := VG.Proof.MlKem.X86.rate_lt hr; omega) h.bufs.bS post)
    rw [VG.Proof.MlKem.X86.pad_stack, h.esp] at hr'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, below_sub (by omega) hE⟩
    · exact ⟨_, by simp, below_sub (by simp) hE⟩

/-- A call of `vg_keccak_squeeze`. -/
theorem squeeze_piece (E S O W : State → BitVec 32) (rate pos len : Nat) (hr : rate ∈ rates) (hp : pos ≤ rate)
    (hlen : len < 2 ^ 32) (hA : ∀ s₀ s, Pre s₀ → A s₀ s → VG.Proof.MlKem.X86.SqueezeAt s (E s₀) (S s₀) (O s₀) (W s₀) rate pos len)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
      E s₀ = E s₀' ∧ S s₀ = S s₀' ∧ O s₀ = O s₀' ∧ W s₀ = W s₀')
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 (S s₀) 200, reg32 (O s₀) len, reg32 (W s₀) 640, below (E s₀) 40] s.mem s'.mem →
      bytesAt s'.mem ((O s₀).setWidth 64) len = squeezeFrom rate (stateAt s.mem ((S s₀).setWidth 64)) pos len →
      (∃ pos' ≤ rate, ∀ d, squeezeFrom rate (stateAt s'.mem ((S s₀).setWidth 64)) pos' d =
        squeezeFrom rate (stateAt s.mem ((S s₀).setWidth 64)) (pos + len) d) → B s₀ s') :
    Piece Pre Pub A B (Impl.MlKem.X86.callWith VG.Proof.MlKem.X86.rs6 "vg_keccak_squeeze_scratch" Impl.Sha3.X86.Stream.squeeze) := by
  refine Piece.callWith Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.1
    Proof.Sha3.X86.Stream.Squeeze.squeeze_verified.2.1 VG.Proof.MlKem.X86.squeeze_nosp (by decide) (by decide)
    (fun _ => []) (fun s₀ => [reg32 (S s₀) 200, reg32 (O s₀) len, reg32 (W s₀) 640, below (E s₀) 24])
    (fun s₀ s h₀ ha => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ha ha' => ?_)
    (fun s₀ s s' h₀ ha e₁ e₂ e₃ fr post => ?_)
  · have h := hA s₀ s h₀ ha
    have := h.bufs.hE
    rw [VG.Proof.MlKem.X86.squeeze_stack, h.esp]; simp only [List.length_cons, List.length_nil]; omega
  · have h := hA s₀ s h₀ ha
    exact VG.Proof.MlKem.X86.squeeze_pre h.esp h.args h.bufs h.fO h.dSO h.dOW h.bO hr hp hlen h.cS h.cO h.cW
  · obtain ⟨e₁, e₂, e₃, e₄⟩ := hpub s₀ s₀' h₀ h₀' hq
    have h := hA s₀ s h₀ ha
    have h' := hA s₀' s' h₀' ha'
    rw [← e₁, ← e₂, ← e₃, ← e₄] at h'
    have hsp : s.gpr .esp = s'.gpr .esp := h.esp.trans h'.esp.symm
    exact ⟨rfl, by rw [e₁, e₂, e₃, e₄], hsp,
      VG.Proof.MlKem.X86.args6_eq (by rw [h.esp]; exact h.bufs.hE) hsp (VG.Proof.MlKem.X86.absArgs_eq h.args h'.args) _ _⟩
  · have h := hA s₀ s h₀ ha
    have hE := h.bufs.hE
    obtain ⟨r₁, r₂⟩ := VG.Proof.MlKem.X86.squeeze_post h.esp h.args hE hlen (VG.Proof.MlKem.X86.rate_lt hr) (by have := VG.Proof.MlKem.X86.rate_lt hr; omega)
      h.bufs.bS post
    refine hQ s₀ s s' h₀ ha e₁ e₂ e₃ (fr.sub fun r hr' => ?_) r₁ r₂
    rw [VG.Proof.MlKem.X86.squeeze_stack, h.esp] at hr'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, below_sub (by omega) hE⟩
    · exact ⟨_, by simp, below_sub (by simp) hE⟩

end

end VG.Proof.MlKem.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.SampleSetup`. -/
section

/-!
# ML-KEM on x86 (32-bit): the SHAKE128 output of `vg_mlkem_sample_ntt`

`vg_mlkem_sample_ntt(seed, a, scratch)` loads `scratch` into `esi`
(`ld_piece`), zeros the Keccak state at `scratch + 840` (`zero_piece`), and
absorbs the 34 bytes of the seed, pads, and squeezes 840 bytes into `scratch`
with the verified Keccak functions (`absorb_call`, `pad_call`,
`squeeze_call`), leaving the first 840 bytes of the XOF output of the seed
there (`Out`).

The state `Base` is what holds throughout the body: `esp` as the leaf's
frame left it, the permissions, and memory changed only in `a`, `scratch`
and the 40 bytes of stack below the frame that the calls use (`W`).
-/

namespace VG.Proof.MlKem.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt stateAt Repr)

section
variable (s₀ : State)
abbrev dP : BitVec 32 := arg s₀ 0
abbrev aP : BitVec 32 := arg s₀ 1
abbrev sP : BitVec 32 := arg s₀ 2
abbrev dA : Addr := (VG.Proof.MlKem.X86.Sample.dP s₀).setWidth 64
abbrev aA : Addr := (VG.Proof.MlKem.X86.Sample.aP s₀).setWidth 64
abbrev sA : Addr := (VG.Proof.MlKem.X86.Sample.sP s₀).setWidth 64
abbrev dR : Region := ⟨VG.Proof.MlKem.X86.Sample.dA s₀, 34⟩
abbrev sR : Region := ⟨VG.Proof.MlKem.X86.Sample.sA s₀, 2048⟩
abbrev gR : Region := ⟨argAddr s₀ 0, 12⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 56#64, 56⟩
/-- The seed. -/
abbrev Bs : List Byte := bytesAt s₀.mem (VG.Proof.MlKem.X86.Sample.dA s₀) 34
/-- `esp` in the body. -/
abbrev E1 : BitVec 32 := (P0 s₀).gpr .esp
/-- The stack the calls use. -/
abbrev cR : Region := below (VG.Proof.MlKem.X86.Sample.E1 s₀) 40
/-- The Keccak state. -/
abbrev SS : BitVec 32 := VG.Proof.MlKem.X86.Sample.sP s₀ + BitVec.ofNat 32 840
/-- The Keccak functions' working space. -/
abbrev WW : BitVec 32 := VG.Proof.MlKem.X86.Sample.sP s₀ + BitVec.ofNat 32 1040
/-- What the body may change. -/
abbrev W : List Region := [polyRegion (VG.Proof.MlKem.X86.Sample.aA s₀), VG.Proof.MlKem.X86.Sample.sR s₀, VG.Proof.MlKem.X86.Sample.cR s₀]
end

structure Pre (s₀ : State) : Prop where
  sp : 56 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 12 ≤ 2 ^ 32
  rd : s₀.rd = [VG.Proof.MlKem.X86.Sample.dR s₀]
  wr : s₀.wr = [polyRegion (VG.Proof.MlKem.X86.Sample.aA s₀), VG.Proof.MlKem.X86.Sample.sR s₀, VG.Proof.MlKem.X86.Sample.gR s₀]
  d_a : (VG.Proof.MlKem.X86.Sample.dR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.Sample.aA s₀))
  d_s : (VG.Proof.MlKem.X86.Sample.dR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.sR s₀)
  d_g : (VG.Proof.MlKem.X86.Sample.dR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.gR s₀)
  a_s : (polyRegion (VG.Proof.MlKem.X86.Sample.aA s₀)).Disjoint (VG.Proof.MlKem.X86.Sample.sR s₀)
  a_g : (polyRegion (VG.Proof.MlKem.X86.Sample.aA s₀)).Disjoint (VG.Proof.MlKem.X86.Sample.gR s₀)
  s_g : (VG.Proof.MlKem.X86.Sample.sR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.gR s₀)
  ret_d : (VG.Proof.MlKem.X86.retR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.dR s₀)
  ret_a : (VG.Proof.MlKem.X86.retR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.Sample.aA s₀))
  ret_s : (VG.Proof.MlKem.X86.retR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.sR s₀)
  ret_g : (VG.Proof.MlKem.X86.retR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.gR s₀)
  stk_d : (VG.Proof.MlKem.X86.Sample.stkR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.dR s₀)
  stk_a : (VG.Proof.MlKem.X86.Sample.stkR s₀).Disjoint (polyRegion (VG.Proof.MlKem.X86.Sample.aA s₀))
  stk_s : (VG.Proof.MlKem.X86.Sample.stkR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.sR s₀)
  stk_g : (VG.Proof.MlKem.X86.Sample.stkR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.gR s₀)
  d_fit : (VG.Proof.MlKem.X86.Sample.dP s₀).toNat + 34 ≤ 2 ^ 32
  a_fit : (VG.Proof.MlKem.X86.Sample.aP s₀).toNat + 1024 ≤ 2 ^ 32
  s_fit : (VG.Proof.MlKem.X86.Sample.sP s₀).toNat + 2048 ≤ 2 ^ 32

theorem Pre.of {s₀ : State} (h : (sampleNTTContract X86.abi 56).pre s₀) : VG.Proof.MlKem.X86.Sample.Pre s₀ := by
  sig_pre [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩

/-- The pointers, `esp` and the seed agree. -/
def Pub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ VG.Proof.MlKem.X86.Sample.Bs s₀ = VG.Proof.MlKem.X86.Sample.Bs s₀' ∧ VG.Proof.MlKem.X86.Sample.dP s₀ = VG.Proof.MlKem.X86.Sample.dP s₀' ∧ VG.Proof.MlKem.X86.Sample.aP s₀ = VG.Proof.MlKem.X86.Sample.aP s₀' ∧ VG.Proof.MlKem.X86.Sample.sP s₀ = VG.Proof.MlKem.X86.Sample.sP s₀'

theorem Pub.E1 {s₀ s₀' : State} (hq : VG.Proof.MlKem.X86.Sample.Pub s₀ s₀') : VG.Proof.MlKem.X86.Sample.E1 s₀ = VG.Proof.MlKem.X86.Sample.E1 s₀' := by
  simp only [P0_esp, hq.1]

/-! ## Regions -/

/-- The `a` bytes below `sp` and the `b` bytes below them. -/
theorem below_adj {sp : BitVec 32} {a b : Nat} (h : a + b ≤ sp.toNat) :
    (below sp a).Disjoint (below (sp - BitVec.ofNat 32 a) b) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have hk : b ≤ (sp - BitVec.ofNat 32 a).toNat := by rw [sub_toNat (by omega)]; omega
  rw [Taint.sub_setWidth (by omega)] at h₁
  rw [Taint.sub_setWidth hk, Taint.sub_setWidth (by omega)] at h₂
  have := sp.isLt
  have hE : (sp.setWidth 64).toNat = sp.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize sp.setWidth 64 = E at *
  bv_omega

/-- The return address and the stack below it. -/
theorem ret_below {sp : BitVec 32} {n : Nat} (h : n ≤ sp.toNat) :
    (⟨sp.setWidth 64, 4⟩ : Region).Disjoint (below sp n) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth h] at h₂
  have := sp.isLt
  have hE : (sp.setWidth 64).toNat = sp.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize sp.setWidth 64 = E at *
  bv_omega

/-- Two parts of a region at a 32-bit pointer that do not overlap. -/
theorem disj_at {x : BitVec 32} {len a b n k : Nat} (ha : a + n ≤ len) (hb : b + k ≤ len)
    (hx : x.toNat + len ≤ 2 ^ 32) (h : a + n ≤ b ∨ b + k ≤ a) :
    (⟨x.setWidth 64 + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨x.setWidth 64 + BitVec.ofNat 64 b, k⟩ :=
  fun y h₁ h₂ => sep_at ha hb hx h y (by simp only [Region.Contains] at h₁; omega)
    (by simp only [Region.Contains] at h₂; omega)

theorem toNat_off {x : BitVec 32} {o : Nat} (h : x.toNat + o < 2 ^ 32) :
    (x + BitVec.ofNat 32 o).toNat = x.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt h]

theorem esp_nat (s₀ : State) (h : 16 ≤ (E0 s₀).toNat) : (VG.Proof.MlKem.X86.Sample.E1 s₀).toNat = (E0 s₀).toNat - 16 := by
  rw [VG.Proof.MlKem.X86.Sample.E1, P0_esp]; exact sub_toNat (k := 16) h

namespace Pre
variable {s₀ : State} (hp : VG.Proof.MlKem.X86.Sample.Pre s₀)
include hp

theorem stk_below : VG.Proof.MlKem.X86.Sample.stkR s₀ = below (E0 s₀) 56 := by
  simp only [VG.Proof.MlKem.X86.Sample.stkR, below]; rw [Taint.sub_setWidth hp.sp]

theorem frame_sub : Region.Sub (frameR s₀) (VG.Proof.MlKem.X86.Sample.stkR s₀) := by
  rw [hp.stk_below]; exact below_sub (by omega) hp.sp

omit hp in
theorem cR_eq : VG.Proof.MlKem.X86.Sample.cR s₀ = below (E0 s₀ - BitVec.ofNat 32 16) 40 := by
  show below ((P0 s₀).gpr .esp) 40 = _
  rw [P0_esp]; rfl

theorem c_sub : Region.Sub (VG.Proof.MlKem.X86.Sample.cR s₀) (VG.Proof.MlKem.X86.Sample.stkR s₀) := by
  rw [hp.stk_below, VG.Proof.MlKem.X86.Sample.Pre.cR_eq]
  exact below_inner (sp := E0 s₀) (a := 40) (b := 56) (k := 16) (by omega) hp.sp

theorem frame_c : (frameR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.cR s₀) := VG.Proof.MlKem.X86.Sample.Pre.cR_eq (s₀ := s₀) ▸ VG.Proof.MlKem.X86.Sample.below_adj (sp := E0 s₀) (a := 16) (b := 40) (by have := hp.sp; omega)

theorem ret_c : (VG.Proof.MlKem.X86.retR s₀).Disjoint (VG.Proof.MlKem.X86.Sample.cR s₀) :=
  (hp.stk_below ▸ VG.Proof.MlKem.X86.Sample.ret_below (sp := E0 s₀) hp.sp).sub_right hp.c_sub

theorem fr16 : (⟨(E0 s₀).setWidth 64 - 16#64, 16⟩ : Region) = frameR s₀ := by
  simp only [frameR, below]; rw [Taint.sub_setWidth (by have := hp.sp; omega)]

theorem hW : ∀ r ∈ VG.Proof.MlKem.X86.Sample.W s₀, (frameR s₀).Disjoint r ∧ (VG.Proof.MlKem.X86.retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨hp.stk_a.sub_left hp.frame_sub, hp.ret_a⟩
  · exact ⟨hp.stk_s.sub_left hp.frame_sub, hp.ret_s⟩
  · exact ⟨hp.frame_c, hp.ret_c⟩

theorem dW : ∀ r ∈ VG.Proof.MlKem.X86.Sample.W s₀, (VG.Proof.MlKem.X86.Sample.dR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.d_a
  · exact hp.d_s
  · exact (hp.stk_d.sub_left hp.c_sub).symm

theorem gW : ∀ r ∈ VG.Proof.MlKem.X86.Sample.W s₀, (VG.Proof.MlKem.X86.Sample.gR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_g.symm
  · exact hp.s_g.symm
  · exact (hp.stk_g.sub_left hp.c_sub).symm

theorem sub_s {o n : Nat} (h : o + n ≤ 2048) : Region.Sub ⟨VG.Proof.MlKem.X86.Sample.sA s₀ + BitVec.ofNat 64 o, n⟩ (VG.Proof.MlKem.X86.Sample.sR s₀) :=
  sub_of_contains (contains_at h hp.s_fit)

theorem off_eq {o : Nat} (h : o < 2048) : (VG.Proof.MlKem.X86.Sample.sP s₀ + BitVec.ofNat 32 o).setWidth 64 = VG.Proof.MlKem.X86.Sample.sA s₀ + BitVec.ofNat 64 o :=
  ea_off (by have := hp.s_fit; omega)

theorem reg_s {o n : Nat} (h : o < 2048) :
    reg32 (VG.Proof.MlKem.X86.Sample.sP s₀ + BitVec.ofNat 32 o) n = ⟨VG.Proof.MlKem.X86.Sample.sA s₀ + BitVec.ofNat 64 o, n⟩ := by
  show (⟨(VG.Proof.MlKem.X86.Sample.sP s₀ + BitVec.ofNat 32 o).setWidth 64, n⟩ : Region) = _
  rw [hp.off_eq h]

omit hp in
theorem reg_s0 {n : Nat} : reg32 (VG.Proof.MlKem.X86.Sample.sP s₀) n = ⟨VG.Proof.MlKem.X86.Sample.sA s₀ + BitVec.ofNat 64 0, n⟩ := by
  show (⟨(VG.Proof.MlKem.X86.Sample.sP s₀).setWidth 64, n⟩ : Region) = _
  simp only [BitVec.add_zero]

/-- The push changes nothing but the frame. -/
theorem P0_keep : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact Nat.le_trans (by decide) hp.sp)
  rw [saveRegs_len] at hf
  exact hf

theorem seed0 : bytesAt (P0 s₀).mem (VG.Proof.MlKem.X86.Sample.dA s₀) 34 = VG.Proof.MlKem.X86.Sample.Bs s₀ :=
  bytesAt_frame hp.P0_keep (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.stk_d.sub_left hp.frame_sub).symm) (by decide)

theorem kbufs : VG.Proof.MlKem.X86.KBufs (VG.Proof.MlKem.X86.Sample.E1 s₀) (VG.Proof.MlKem.X86.Sample.SS s₀) (VG.Proof.MlKem.X86.Sample.WW s₀) := by
  have hs := hp.s_fit
  have e := VG.Proof.MlKem.X86.Sample.esp_nat s₀ (by have := hp.sp; omega)
  have hsp := hp.sp
  refine ⟨by rw [e]; omega, by rw [VG.Proof.MlKem.X86.Sample.toNat_off (by omega)]; omega, by rw [VG.Proof.MlKem.X86.Sample.toNat_off (by omega)]; omega, ?_, ?_, ?_⟩
  · rw [hp.reg_s (by omega), hp.reg_s (by omega)]
    exact VG.Proof.MlKem.X86.Sample.disj_at (len := 2048) (by omega) (by omega) hs (by omega)
  · rw [hp.reg_s (by omega)]
    exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega))
  · rw [hp.reg_s (by omega)]
    exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega))

theorem within_s {s : State} (hw : s.wr = (P0 s₀).wr) {o n : Nat} (ho : o < 2048) (h : o + n ≤ 2048) :
    VG.Proof.MlKem.X86.Within (reg32 (VG.Proof.MlKem.X86.Sample.sP s₀ + BitVec.ofNat 32 o) n) s.wr := by
  rw [hp.reg_s ho]
  exact ⟨VG.Proof.MlKem.X86.Sample.sR s₀, by rw [hw, P0_wr, hp.wr]; simp, o, rfl, h⟩

theorem within_s0 {s : State} (hw : s.wr = (P0 s₀).wr) {n : Nat} (h : n ≤ 2048) :
    VG.Proof.MlKem.X86.Within (reg32 (VG.Proof.MlKem.X86.Sample.sP s₀) n) s.wr := by
  rw [Pre.reg_s0]
  exact ⟨VG.Proof.MlKem.X86.Sample.sR s₀, by rw [hw, P0_wr, hp.wr]; simp, 0, rfl, by simpa using h⟩

end Pre

/-! ## What holds throughout the body -/

structure Base (s₀ s : State) : Prop where
  esp : s.gpr .esp = VG.Proof.MlKem.X86.Sample.E1 s₀
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  frame : Frame (VG.Proof.MlKem.X86.Sample.W s₀) (P0 s₀).mem s.mem

/-- `Base`, with `esi = scratch`. -/
structure Ctx (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Sample.Base s₀ s where
  esi : s.gpr .esi = VG.Proof.MlKem.X86.Sample.sP s₀

namespace Base
variable {s₀ s : State} (hp : VG.Proof.MlKem.X86.Sample.Pre s₀) (h : VG.Proof.MlKem.X86.Sample.Base s₀ s)
include hp h

theorem seed : bytesAt s.mem (VG.Proof.MlKem.X86.Sample.dA s₀) 34 = VG.Proof.MlKem.X86.Sample.Bs s₀ :=
  (bytesAt_frame h.frame hp.dW (by decide)).trans hp.seed0

theorem argw {i : Nat} (hi : i < 3) : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have fit := hp.sp'
  rw [h.frame.readW (VG.Proof.MlKem.X86.arg_contains (n := 3) hi fit) hp.gW (by decide)]
  exact P0_arg (by have := hp.sp; omega) hi fit (by rw [hp.fr16]; exact (hp.stk_g.sub_left hp.frame_sub))

theorem argIn {i : Nat} (hi : i < 3) : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [h.rd, h.wr]
  exact P0_argIn hi hp.sp' (by simp [hp.wr])

omit hp in
theorem argEa {i : Nat} : (s.gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i := by
  rw [h.esp]; exact P0_argAddr s₀ i

omit hp in
/-- After a call that changes memory only within `rs`, parts of `W`. -/
theorem call {s' : State} (e₁ : s'.rd = s.rd) (e₂ : s'.wr = s.wr)
    (e₃ : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {rs : List Region} (fr : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.MlKem.X86.Sample.W s₀, Region.Sub r r') : VG.Proof.MlKem.X86.Sample.Base s₀ s' :=
  ⟨by rw [e₃ .esp (by simp [calleeSaved]), h.esp], by rw [e₁, h.rd], by rw [e₂, h.wr],
    h.frame.trans (fr.sub hs)⟩

end Base

theorem Ctx.call {s₀ s s' : State} (h : VG.Proof.MlKem.X86.Sample.Ctx s₀ s) (e₁ : s'.rd = s.rd) (e₂ : s'.wr = s.wr)
    (e₃ : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {rs : List Region} (fr : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.MlKem.X86.Sample.W s₀, Region.Sub r r') : VG.Proof.MlKem.X86.Sample.Ctx s₀ s' :=
  ⟨h.toBase.call e₁ e₂ e₃ fr hs, by rw [e₃ .esi (by simp [calleeSaved]), h.esi]⟩

/-- The regions a call of the Keccak functions changes are parts of `W`. -/
theorem calls_sub {s₀ : State} (hp : VG.Proof.MlKem.X86.Sample.Pre s₀) :
    ∀ r ∈ [reg32 (VG.Proof.MlKem.X86.Sample.SS s₀) 200, reg32 (VG.Proof.MlKem.X86.Sample.sP s₀) 840, reg32 (VG.Proof.MlKem.X86.Sample.WW s₀) 640, below (VG.Proof.MlKem.X86.Sample.E1 s₀) 40],
      ∃ r' ∈ VG.Proof.MlKem.X86.Sample.W s₀, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨VG.Proof.MlKem.X86.Sample.sR s₀, by simp, by rw [hp.reg_s (by omega)]; exact hp.sub_s (by omega)⟩
  · exact ⟨VG.Proof.MlKem.X86.Sample.sR s₀, by simp, by rw [Pre.reg_s0]; exact hp.sub_s (by omega)⟩
  · exact ⟨VG.Proof.MlKem.X86.Sample.sR s₀, by simp, by rw [hp.reg_s (by omega)]; exact hp.sub_s (by omega)⟩
  · exact ⟨VG.Proof.MlKem.X86.Sample.cR s₀, by simp, fun _ h => h⟩

theorem calls_sub3 {s₀ : State} (hp : VG.Proof.MlKem.X86.Sample.Pre s₀) :
    ∀ r ∈ [reg32 (VG.Proof.MlKem.X86.Sample.SS s₀) 200, reg32 (VG.Proof.MlKem.X86.Sample.WW s₀) 640, below (VG.Proof.MlKem.X86.Sample.E1 s₀) 40], ∃ r' ∈ VG.Proof.MlKem.X86.Sample.W s₀, Region.Sub r r' :=
  fun r hr => VG.Proof.MlKem.X86.Sample.calls_sub hp r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp [h])

/-! ## `esi = scratch` -/

theorem ld_piece : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlKem.X86.Sample.Ctx (.block [.mov .esi (.mem (at_ .esp 28))]) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have b₀ : VG.Proof.MlKem.X86.Sample.Base s₀ (P0 s₀) := ⟨rfl, rfl, rfl, Frame.refl _ _⟩
    have a₂ := b₀.argEa (i := 2)
    have i₂ := b₀.argIn hp (i := 2) (by omega)
    have v₂ := b₀.argw hp (i := 2) (by omega)
    simp only [Nat.reduceMul, Nat.reduceAdd] at a₂
    apply WP.of_runBlock
    simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea,
      State.load32, State.setReg, Option.map_some, a₂, i₂, v₂, ite_true, Option.some.injEq,
      exists_eq_left']
    exact ⟨⟨by simp, rfl, rfl, Frame.refl _ _⟩, by simp⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

/-! ## The Keccak state set to zero -/

/-- After `k` words. -/
structure ZInv (s₀ : State) (k : Nat) (s : State) : Prop extends VG.Proof.MlKem.X86.Sample.Ctx s₀ s where
  ebx : s.gpr .ebx = VG.Proof.MlKem.X86.Sample.SS s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (50 - k)
  eax : s.gpr .eax = 0
  zero : ∀ j < 4 * k, s.mem ((VG.Proof.MlKem.X86.Sample.SS s₀).setWidth 64 + BitVec.ofNat 64 j) = 0

theorem zinit_piece : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub VG.Proof.MlKem.X86.Sample.Ctx (VG.Proof.MlKem.X86.Sample.ZInv · 0) (.block (zeroInit smpSt)) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [zeroInit, smpSt, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.map_some, Option.bind_some, State.setReg, arithFlags, State.setFlags, Option.some.injEq,
    exists_eq_left']
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, by simp [h.esi]⟩, by simp [h.esi], by simp, by simp,
    fun j hj => absurd hj (by omega)⟩

theorem zero_write {m : Mem} {a : Addr} {k : Nat}
    (h : ∀ j < 4 * k, m (a + BitVec.ofNat 64 j) = 0) :
    ∀ j < 4 * (k + 1), (m.writeW (a + BitVec.ofNat 64 (4 * k)) (0 : BitVec 32)) (a + BitVec.ofNat 64 j) = 0 := by
  intro j hj
  simp only [Mem.writeW, Mem.write]
  split
  · simp
  · rename_i hn
    refine h j (Nat.lt_of_not_le fun hc => hn ?_)
    rw [show a + BitVec.ofNat 64 j - (a + BitVec.ofNat 64 (4 * k)) = BitVec.ofNat 64 (j - 4 * k) by
      rw [show j = 4 * k + (j - 4 * k) by omega, BitVec.ofNat_add]; bv_omega]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega

theorem zstep {s₀ : State} (hp : VG.Proof.MlKem.X86.Sample.Pre s₀) {k : Nat} (hk : k < 50) {s : State} (h : VG.Proof.MlKem.X86.Sample.ZInv s₀ k s) :
    WP isa (.block zeroBody) s fun s' => VG.Proof.MlKem.X86.Sample.ZInv s₀ (k + 1) s' ∧ VG.X86.eval .ne s' = some (decide (k + 1 < 50)) := by
  have hs := hp.s_fit
  have tS : (VG.Proof.MlKem.X86.Sample.SS s₀).toNat = (VG.Proof.MlKem.X86.Sample.sP s₀).toNat + 840 := VG.Proof.MlKem.X86.Sample.toNat_off (by omega)
  have ea : (VG.Proof.MlKem.X86.Sample.SS s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 =
      (VG.Proof.MlKem.X86.Sample.SS s₀).setWidth 64 + BitVec.ofNat 64 (4 * k) := by
    rw [ea_add (by omega)]; rfl
  have eS : (VG.Proof.MlKem.X86.Sample.SS s₀).setWidth 64 = VG.Proof.MlKem.X86.Sample.sA s₀ + BitVec.ofNat 64 840 := hp.off_eq (by omega)
  have hin : InRegions s.wr ((VG.Proof.MlKem.X86.Sample.SS s₀).setWidth 64 + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [eS, BitVec.add_assoc, ← BitVec.ofNat_add, h.wr, P0_wr, hp.wr]
    exact ⟨VG.Proof.MlKem.X86.Sample.sR s₀, by simp, contains_at (by omega) hs⟩
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, zeroBody, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, State.ea, State.store32, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, h.ebx, ea, hin, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, ?_⟩, by simp [h.esi]⟩, ?_, ?_, by simp [h.eax], ?_⟩, ?_⟩
  · refine h.frame.writeW (r := VG.Proof.MlKem.X86.Sample.sR s₀) (by simp) _ ?_
    rw [eS, BitVec.add_assoc, ← BitVec.ofNat_add]; exact contains_at (by omega) hs
  · simp only [ite_true]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx]
    exact cnt_next hk
  · rw [h.eax]; exact VG.Proof.MlKem.X86.Sample.zero_write h.zero
  · simp only [VG.X86.eval, h.ecx]
    exact cnt_ne hk (by omega)

theorem zloop_piece : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub (VG.Proof.MlKem.X86.Sample.ZInv · 0) (VG.Proof.MlKem.X86.Sample.ZInv · 50) (.loop (.block zeroBody) .ne) :=
  Piece.countLoop (by decide) (fun k s₀ s => VG.Proof.MlKem.X86.Sample.ZInv s₀ k s) [.ebx]
    (fun k hk s₀ s hp h => VG.Proof.MlKem.X86.Sample.zstep hp hk h)
    (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.ebx, h'.ebx, VG.Proof.MlKem.X86.Sample.SS, VG.Proof.MlKem.X86.Sample.SS, hq.2.2.2.2]) (by taint_decide)

theorem stateAt_zero {m : Mem} {p : Addr} (h : ∀ j < 200, m (p + BitVec.ofNat 64 j) = 0) :
    stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  rw [Mem.readW_congr (m' := fun _ => 0) fun b hb => ?_]
  · simp [Mem.readW, Mem.read]
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)

/-- `Ctx`, with the Keccak state zero. -/
structure Z (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Sample.Ctx s₀ s where
  st : stateAt s.mem ((VG.Proof.MlKem.X86.Sample.SS s₀).setWidth 64) = Spec.Sha3.zero

theorem zero_piece : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub VG.Proof.MlKem.X86.Sample.Ctx VG.Proof.MlKem.X86.Sample.Z (zeroSt smpSt) :=
  (Piece.seq VG.Proof.MlKem.X86.Sample.zinit_piece VG.Proof.MlKem.X86.Sample.zloop_piece).mono (fun _ _ _ h => h)
    fun _ _ _ h => ⟨h.toCtx, VG.Proof.MlKem.X86.Sample.stateAt_zero fun j hj => h.zero j (by omega)⟩

end VG.Proof.MlKem.X86.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.SampleCalls`. -/
section

/-!
# ML-KEM on x86 (32-bit): the Keccak calls of `vg_mlkem_sample_ntt`

From the all-zero state (`Z`), absorbing the seed (`absorb_call`), padding for
SHAKE128 (`pad_call`) and squeezing 840 bytes into `scratch` (`squeeze_call`)
leaves the first 840 bytes of the XOF output of the seed there (`Out`). Each
call's arguments are set by a block (`absArgs_piece`, `padArgs_piece`,
`sqArgs_piece`) from `esi = scratch` and the seed pointer on the stack.
-/

namespace VG.Proof.MlKem.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt stateAt Repr squeezeFrom shakeSuffix)

/-! ## Absorbing the seed -/

theorem absArgs_piece : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub VG.Proof.MlKem.X86.Sample.Z (fun s₀ s => VG.Proof.MlKem.X86.Sample.Z s₀ s ∧ VG.Proof.MlKem.X86.AbsArgs s (VG.Proof.MlKem.X86.Sample.SS s₀) (VG.Proof.MlKem.X86.Sample.dP s₀) (VG.Proof.MlKem.X86.Sample.WW s₀) 168 0 34)
    (.block smpAbsorbArgs) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have a₀ := h.argEa (i := 0)
    have i₀ := h.argIn hp (i := 0) (by omega)
    have v₀ := h.argw hp (i := 0) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at a₀
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, smpAbsorbArgs, smpSt, smpWk, at_, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a₀, i₀, v₀, Option.some.injEq, exists_eq_left']
    exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, by simp [h.esi]⟩, h.st⟩,
      ⟨by simp [h.esi], rfl, rfl, rfl, rfl, by simp [h.esi]⟩⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.E1]

/-- `Ctx`, with the seed absorbed. -/
structure A1 (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Sample.Ctx s₀ s where
  st : Repr s.mem ((VG.Proof.MlKem.X86.Sample.SS s₀).setWidth 64) 168 (VG.Proof.MlKem.X86.Sample.Bs s₀)

theorem absorb_call : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub (fun s₀ s => VG.Proof.MlKem.X86.Sample.Z s₀ s ∧ VG.Proof.MlKem.X86.AbsArgs s (VG.Proof.MlKem.X86.Sample.SS s₀) (VG.Proof.MlKem.X86.Sample.dP s₀) (VG.Proof.MlKem.X86.Sample.WW s₀) 168 0 34) VG.Proof.MlKem.X86.Sample.A1
    (callWith VG.Proof.MlKem.X86.rs6 "vg_keccak_absorb_scratch" Impl.Sha3.X86.Stream.absorb) := by
  refine VG.Proof.MlKem.X86.absorb_piece VG.Proof.MlKem.X86.Sample.E1 VG.Proof.MlKem.X86.Sample.SS VG.Proof.MlKem.X86.Sample.dP VG.Proof.MlKem.X86.Sample.WW 168 0 34 rate168 (by decide) (by decide) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, by rw [VG.Proof.MlKem.X86.Sample.SS, VG.Proof.MlKem.X86.Sample.SS, hq.2.2.2.2], hq.2.2.1, by rw [VG.Proof.MlKem.X86.Sample.WW, VG.Proof.MlKem.X86.Sample.WW, hq.2.2.2.2]⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr post => ?_)
  · have hk := hp.kbufs
    have hs := hp.s_fit
    refine ⟨h.esp, ha, hk, hp.d_fit, ?_, ?_, (hp.stk_d.sub_left hp.c_sub), ?_, hp.within_s h.wr (by omega) (by omega),
      hp.within_s h.wr (by omega) (by omega)⟩
    · rw [hp.reg_s (by omega)]; exact hp.d_s.sub_right (hp.sub_s (by omega))
    · rw [hp.reg_s (by omega)]; exact hp.d_s.sub_right (hp.sub_s (by omega))
    · refine ⟨VG.Proof.MlKem.X86.Sample.dR s₀, ?_, 0, (BitVec.add_zero _).symm, Nat.le_refl _⟩
      rw [h.rd, h.wr, pushed_rd, hp.rd]; simp
  · refine ⟨h.toCtx.call e₁ e₂ e₃ fr (VG.Proof.MlKem.X86.Sample.calls_sub3 hp), ?_⟩
    have := post [] (repr_nil h.st) (by simp)
    rwa [List.nil_append, h.seed hp] at this

/-! ## Padding -/

theorem padArgs_piece : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub VG.Proof.MlKem.X86.Sample.A1 (fun s₀ s => VG.Proof.MlKem.X86.Sample.A1 s₀ s ∧ VG.Proof.MlKem.X86.PadArgs s (VG.Proof.MlKem.X86.Sample.SS s₀) (VG.Proof.MlKem.X86.Sample.WW s₀) 168 34 0x1f)
    (.block smpPadArgs) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, smpPadArgs, smpSt, smpWk, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, by simp [h.esi]⟩, h.st⟩,
    ⟨by simp [h.esi], rfl, rfl, rfl, by simp [h.esi]⟩⟩

/-- `Ctx`, with the seed absorbed and padded for SHAKE128. -/
structure A2 (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Sample.Ctx s₀ s where
  st : stateAt s.mem ((VG.Proof.MlKem.X86.Sample.SS s₀).setWidth 64) = padded 168 shakeSuffix (VG.Proof.MlKem.X86.Sample.Bs s₀)

theorem pad_call : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub (fun s₀ s => VG.Proof.MlKem.X86.Sample.A1 s₀ s ∧ VG.Proof.MlKem.X86.PadArgs s (VG.Proof.MlKem.X86.Sample.SS s₀) (VG.Proof.MlKem.X86.Sample.WW s₀) 168 34 0x1f) VG.Proof.MlKem.X86.Sample.A2
    (callWith VG.Proof.MlKem.X86.rs5 "vg_keccak_pad_scratch" Impl.Sha3.X86.Stream.pad) := by
  refine VG.Proof.MlKem.X86.pad_piece VG.Proof.MlKem.X86.Sample.E1 VG.Proof.MlKem.X86.Sample.SS VG.Proof.MlKem.X86.Sample.WW 168 34 0x1f rate168 (by decide) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, by rw [VG.Proof.MlKem.X86.Sample.SS, VG.Proof.MlKem.X86.Sample.SS, hq.2.2.2.2], by rw [VG.Proof.MlKem.X86.Sample.WW, VG.Proof.MlKem.X86.Sample.WW, hq.2.2.2.2]⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr post => ?_)
  · exact ⟨h.esp, ha, hp.kbufs, hp.within_s h.wr (by omega) (by omega), hp.within_s h.wr (by omega) (by omega)⟩
  · refine ⟨h.toCtx.call e₁ e₂ e₃ fr (VG.Proof.MlKem.X86.Sample.calls_sub3 hp), ?_⟩
    have := post (VG.Proof.MlKem.X86.Sample.Bs s₀) h.st (by rw [bytesAt_length])
    rwa [show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32] at this

/-! ## Squeezing -/

theorem sqArgs_piece : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub VG.Proof.MlKem.X86.Sample.A2 (fun s₀ s => VG.Proof.MlKem.X86.Sample.A2 s₀ s ∧ VG.Proof.MlKem.X86.AbsArgs s (VG.Proof.MlKem.X86.Sample.SS s₀) (VG.Proof.MlKem.X86.Sample.sP s₀) (VG.Proof.MlKem.X86.Sample.WW s₀) 168 0 840)
    (.block smpSqueezeArgs) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, smpSqueezeArgs, smpSt, smpWk, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, by simp [h.esi]⟩, h.st⟩,
    ⟨by simp [h.esi], rfl, rfl, by simp [h.esi], rfl, by simp [h.esi]⟩⟩

/-- `Ctx`, with the first 840 bytes of the XOF output of the seed at `scratch`. -/
structure Out (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Sample.Ctx s₀ s where
  out : ∀ p < 840, s.mem (VG.Proof.MlKem.X86.Sample.sA s₀ + BitVec.ofNat 64 p) = xofByte (VG.Proof.MlKem.X86.Sample.Bs s₀) p

theorem squeeze_call : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub (fun s₀ s => VG.Proof.MlKem.X86.Sample.A2 s₀ s ∧ VG.Proof.MlKem.X86.AbsArgs s (VG.Proof.MlKem.X86.Sample.SS s₀) (VG.Proof.MlKem.X86.Sample.sP s₀) (VG.Proof.MlKem.X86.Sample.WW s₀) 168 0 840) VG.Proof.MlKem.X86.Sample.Out
    (callWith VG.Proof.MlKem.X86.rs6 "vg_keccak_squeeze_scratch" Impl.Sha3.X86.Stream.squeeze) := by
  refine VG.Proof.MlKem.X86.squeeze_piece VG.Proof.MlKem.X86.Sample.E1 VG.Proof.MlKem.X86.Sample.SS VG.Proof.MlKem.X86.Sample.sP VG.Proof.MlKem.X86.Sample.WW 168 0 840 rate168 (by decide) (by decide) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, by rw [VG.Proof.MlKem.X86.Sample.SS, VG.Proof.MlKem.X86.Sample.SS, hq.2.2.2.2], hq.2.2.2.2, by rw [VG.Proof.MlKem.X86.Sample.WW, VG.Proof.MlKem.X86.Sample.WW, hq.2.2.2.2]⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr r₁ _ => ?_)
  · have hs := hp.s_fit
    refine ⟨h.esp, ha, hp.kbufs, by omega, ?_, ?_, ?_, hp.within_s h.wr (by omega) (by omega),
      hp.within_s0 h.wr (by omega), hp.within_s h.wr (by omega) (by omega)⟩
    · rw [hp.reg_s (by omega), Pre.reg_s0]
      exact VG.Proof.MlKem.X86.Sample.disj_at (len := 2048) (by omega) (by omega) hs (by omega)
    · rw [hp.reg_s (by omega), Pre.reg_s0]
      exact VG.Proof.MlKem.X86.Sample.disj_at (len := 2048) (by omega) (by omega) hs (by omega)
    · rw [Pre.reg_s0]
      exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega))
  · refine ⟨h.toCtx.call e₁ e₂ e₃ fr (VG.Proof.MlKem.X86.Sample.calls_sub hp), fun p hp' => ?_⟩
    rw [h.st] at r₁
    have e := bytesAt_getD s'.mem (VG.Proof.MlKem.X86.Sample.sA s₀) (len := 840) hp'
    rw [r₁, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [VG.Proof.Sha3.length_squeezeFrom (by decide) (by decide)]; exact hp'),
      Option.getD_some, xof_squeezeFrom_getElem _ hp', Nat.zero_add] at e
    exact e.symm

end VG.Proof.MlKem.X86.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.SampleLoop`. -/
section

/-!
# ML-KEM on x86 (32-bit): the loop of `vg_mlkem_sample_ntt`

After `t` iterations of the loop on the XOF output at `scratch`, the
coefficients accepted, `LA B t = sampleAfter [] (xofByte B) t`
(`Proof/MlKem/KPke.lean`), are at `a`, `edi` points after them and `ecx`
counts them (`Loop`). An iteration computes the candidates `d₁` in `eax` and
`d₂` in `ebx` (`chunk_ok`), and, while there are fewer than 256 coefficients,
accepts each that is less than `q` (`accept_piece`); its branches depend on
the XOF output, which is a function of the seed, and so agree in two runs from
the same seed.
-/

namespace VG.Proof.MlKem.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

/-- The first candidate of chunk `t`. -/
abbrev d₁ (B : List Byte) (t : Nat) : Nat :=
  (xofByte B (3 * t)).toNat + 256 * ((xofByte B (3 * t + 1)).toNat % 16)

/-- The second candidate of chunk `t`. -/
abbrev d₂ (B : List Byte) (t : Nat) : Nat :=
  (xofByte B (3 * t + 1)).toNat / 16 + 16 * (xofByte B (3 * t + 2)).toNat

/-- The coefficients accepted after `t` iterations. -/
abbrev LA (B : List Byte) (t : Nat) : List Zq := sampleAfter [] (xofByte B) t

/-- `L`, with `v` accepted if it is less than `q`. -/
def acc (L : List Zq) (v : Nat) : List Zq := if v < q then L ++ [ofNat v] else L

/-- Coefficient `i` of `L`, as stored. -/
def cv (L : List Zq) (i : Nat) : BitVec 32 := BitVec.ofNat 32 (L.getD i 0).val

theorem d₁_lt (B : List Byte) (t : Nat) : VG.Proof.MlKem.X86.Sample.d₁ B t < 2 ^ 12 := by
  have := (xofByte B (3 * t)).isLt
  have := Nat.mod_lt (xofByte B (3 * t + 1)).toNat (show 16 > 0 by decide)
  simp only [VG.Proof.MlKem.X86.Sample.d₁]; omega

theorem d₂_lt (B : List Byte) (t : Nat) : VG.Proof.MlKem.X86.Sample.d₂ B t < 2 ^ 12 := by
  have := (xofByte B (3 * t + 1)).isLt
  have := (xofByte B (3 * t + 2)).isLt
  simp only [VG.Proof.MlKem.X86.Sample.d₂]; omega

theorem LA_else {B : List Byte} {t : Nat} (h : ¬ (VG.Proof.MlKem.X86.Sample.LA B t).length < 256) : VG.Proof.MlKem.X86.Sample.LA B t = VG.Proof.MlKem.X86.Sample.LA B (t + 1) := by
  have := sampleAfter_length_le (a := []) (Nat.zero_le _) (xofByte B) t
  simp only [VG.Proof.MlKem.X86.Sample.LA] at h ⊢
  rw [sampleAfter_succ, sampleStepCap_full (by rw [n_eq] at this ⊢; omega)]

theorem step_eq (L : List Zq) (c₀ c₁ c₂ : Byte) :
    sampleStep L c₀ c₁ c₂ = (let L₁ := VG.Proof.MlKem.X86.Sample.acc L (c₀.toNat + 256 * (c₁.toNat % 16))
      if L₁.length < 256 then VG.Proof.MlKem.X86.Sample.acc L₁ (c₁.toNat / 16 + 16 * c₂.toNat) else L₁) := by
  unfold sampleStep VG.Proof.MlKem.X86.Sample.acc
  generalize c₀.toNat + 256 * (c₁.toNat % 16) = x
  generalize c₁.toNat / 16 + 16 * c₂.toNat = y
  by_cases hx : x < q <;> by_cases hy : y < q <;> simp [hx, hy, n_eq]

theorem LA_step {B : List Byte} {t : Nat} (h : (VG.Proof.MlKem.X86.Sample.LA B t).length < 256) :
    VG.Proof.MlKem.X86.Sample.LA B (t + 1) = (if (VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.LA B t) (VG.Proof.MlKem.X86.Sample.d₁ B t)).length < 256 then VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.LA B t) (VG.Proof.MlKem.X86.Sample.d₁ B t)) (VG.Proof.MlKem.X86.Sample.d₂ B t)
      else VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.LA B t) (VG.Proof.MlKem.X86.Sample.d₁ B t)) := by
  rw [VG.Proof.MlKem.X86.Sample.LA, sampleAfter_succ, sampleStepCap, ite_eq_right (by rw [n_eq]; exact Nat.ne_of_lt h), VG.Proof.MlKem.X86.Sample.step_eq]

theorem LA_then {B : List Byte} {t : Nat} (h : (VG.Proof.MlKem.X86.Sample.LA B t).length < 256)
    (h₂ : (VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.LA B t) (VG.Proof.MlKem.X86.Sample.d₁ B t)).length < 256) : VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.LA B t) (VG.Proof.MlKem.X86.Sample.d₁ B t)) (VG.Proof.MlKem.X86.Sample.d₂ B t) = VG.Proof.MlKem.X86.Sample.LA B (t + 1) := by
  rw [VG.Proof.MlKem.X86.Sample.LA_step h, ite_eq_left h₂]

theorem LA_then' {B : List Byte} {t : Nat} (h : (VG.Proof.MlKem.X86.Sample.LA B t).length < 256)
    (h₂ : ¬ (VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.LA B t) (VG.Proof.MlKem.X86.Sample.d₁ B t)).length < 256) : VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.LA B t) (VG.Proof.MlKem.X86.Sample.d₁ B t) = VG.Proof.MlKem.X86.Sample.LA B (t + 1) := by
  rw [VG.Proof.MlKem.X86.Sample.LA_step h, ite_eq_right h₂]

theorem acc_len {L : List Zq} {v : Nat} (hv : v < q) : (VG.Proof.MlKem.X86.Sample.acc L v).length = L.length + 1 := by
  simp [VG.Proof.MlKem.X86.Sample.acc, hv]

/-! ## The state of the loop -/

/-- After `t` iterations, with the coefficients `L` accepted. -/
structure Loop (s₀ : State) (t : Nat) (L : List Zq) (s : State) : Prop extends VG.Proof.MlKem.X86.Sample.Base s₀ s where
  out : ∀ p < 840, s.mem (VG.Proof.MlKem.X86.Sample.sA s₀ + BitVec.ofNat 64 p) = xofByte (VG.Proof.MlKem.X86.Sample.Bs s₀) p
  esi : s.gpr .esi = VG.Proof.MlKem.X86.Sample.sP s₀ + BitVec.ofNat 32 (3 * t)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (280 - t)
  len : L.length ≤ 256
  edi : s.gpr .edi = VG.Proof.MlKem.X86.Sample.aP s₀ + BitVec.ofNat 32 (4 * L.length)
  ecx : s.gpr .ecx = BitVec.ofNat 32 L.length
  coef : ∀ i < L.length, coeffAt s.mem (VG.Proof.MlKem.X86.Sample.aA s₀) i = VG.Proof.MlKem.X86.Sample.cv L i

/-- Within iteration `t`, with the second candidate in `ebx`. -/
structure Mid (s₀ : State) (t : Nat) (L : List Zq) (s : State) : Prop extends VG.Proof.MlKem.X86.Sample.Loop s₀ t L s where
  ebx : s.gpr .ebx = BitVec.ofNat 32 (VG.Proof.MlKem.X86.Sample.d₂ (VG.Proof.MlKem.X86.Sample.Bs s₀) t)

theorem Mid.flags {s₀ s s' : State} {t : Nat} {L : List Zq} (h : VG.Proof.MlKem.X86.Sample.Mid s₀ t L s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : VG.Proof.MlKem.X86.Sample.Mid s₀ t L s' :=
  ⟨⟨⟨by rw [hg, h.esp], by rw [hr, h.rd], by rw [hw, h.wr], by rw [hm]; exact h.frame⟩,
    by rw [hm]; exact h.out, by rw [hg, h.esi], by rw [hg, h.ebp], h.len, by rw [hg, h.edi], by rw [hg, h.ecx],
    by rw [hm]; exact h.coef⟩, by rw [hg, h.ebx]⟩

theorem linit_piece : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub VG.Proof.MlKem.X86.Sample.Out (fun s₀ s => VG.Proof.MlKem.X86.Sample.Loop s₀ 0 (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 0) s) (.block smpLoopInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have a₁ := h.argEa (i := 1)
    have i₁ := h.argIn hp (i := 1) (by omega)
    have v₁ := h.argw hp (i := 1) (by omega)
    simp only [Nat.mul_one, Nat.reduceAdd] at a₁
    apply WP.of_runBlock
    simp only [↓reduceIte, smpLoopInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₁, i₁, v₁,
      Option.some.injEq, exists_eq_left']
    exact ⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], rfl, by simp [sampleAfter_zero],
      by simp [sampleAfter_zero], by simp [sampleAfter_zero], fun i hi => by simp [sampleAfter_zero] at hi⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.E1]

/-! ## The candidates -/

theorem chunk_ok {s₀ : State} (hp : VG.Proof.MlKem.X86.Sample.Pre s₀) {t : Nat} (ht : t < 280) {s : State}
    (h : VG.Proof.MlKem.X86.Sample.Loop s₀ t (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) t) s) :
    WP isa (.block smpChunk) s fun s' => VG.Proof.MlKem.X86.Sample.Mid s₀ t (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) t) s' ∧
      s'.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlKem.X86.Sample.d₁ (VG.Proof.MlKem.X86.Sample.Bs s₀) t) ∧
      VG.X86.eval .b s' = some (decide ((VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) t).length < 256)) := by
  have hs := hp.s_fit
  have eb : ∀ o < 3, (VG.Proof.MlKem.X86.Sample.sP s₀ + BitVec.ofNat 32 (3 * t) + BitVec.ofNat 32 o).setWidth 64 =
      VG.Proof.MlKem.X86.Sample.sA s₀ + BitVec.ofNat 64 (3 * t + o) := fun o ho => ea_add (by omega)
  have e0 := eb 0 (by omega)
  have e1 := eb 1 (by omega)
  have e2 := eb 2 (by omega)
  have inS : ∀ o < 3, InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86.Sample.sA s₀ + BitVec.ofNat 64 (3 * t + o)) 1 := fun o ho =>
    ⟨VG.Proof.MlKem.X86.Sample.sR s₀, List.mem_append_right _ (by rw [h.wr, P0_wr, hp.wr]; simp), contains_at (by omega) hs⟩
  have i0 := inS 0 (by omega)
  have i1 := inS 1 (by omega)
  have i2 := inS 2 (by omega)
  have v0 := h.out (3 * t + 0) (by omega)
  have v1 := h.out (3 * t + 1) (by omega)
  have v2 := h.out (3 * t + 2) (by omega)
  simp only [Nat.add_zero] at e0 i0 v0
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self, smpChunk, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, State.ea, State.load8, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, h.esi, e0, e1, e2, i0, i1, i2, v0, v1, v2,
    Option.some.injEq, exists_eq_left']
  have x0 : (BitVec.setWidth 32 (xofByte (VG.Proof.MlKem.X86.Sample.Bs s₀) (3 * t)) +
      (BitVec.setWidth 32 (xofByte (VG.Proof.MlKem.X86.Sample.Bs s₀) (3 * t + 1)) &&& 15).rotateRight 24).toNat = VG.Proof.MlKem.X86.Sample.d₁ (VG.Proof.MlKem.X86.Sample.Bs s₀) t := by
    have l0 := (xofByte (VG.Proof.MlKem.X86.Sample.Bs s₀) (3 * t)).isLt
    have l1 := (xofByte (VG.Proof.MlKem.X86.Sample.Bs s₀) (3 * t + 1)).isLt
    have hm : (BitVec.setWidth 32 (xofByte (VG.Proof.MlKem.X86.Sample.Bs s₀) (3 * t + 1)) &&& 15).toNat =
        (xofByte (VG.Proof.MlKem.X86.Sample.Bs s₀) (3 * t + 1)).toNat % 16 := by
      rw [show (15 : BitVec 32) = BitVec.ofNat 32 (2 ^ 4 - 1) from rfl, toNat_and_mask _ _ (by decide),
        toNat_byte32]
    rw [BitVec.toNat_add, rotr_small _ (by decide) (by decide) (by rw [hm]; omega), hm, toNat_byte32,
      Nat.mod_eq_of_lt (by omega), VG.Proof.MlKem.X86.Sample.d₁]
    omega
  have x1 : (BitVec.setWidth 32 (xofByte (VG.Proof.MlKem.X86.Sample.Bs s₀) (3 * t + 1)) >>> 4 +
      (BitVec.setWidth 32 (xofByte (VG.Proof.MlKem.X86.Sample.Bs s₀) (3 * t + 2))).rotateRight 28).toNat = VG.Proof.MlKem.X86.Sample.d₂ (VG.Proof.MlKem.X86.Sample.Bs s₀) t := by
    have l1 := (xofByte (VG.Proof.MlKem.X86.Sample.Bs s₀) (3 * t + 1)).isLt
    have l2 := (xofByte (VG.Proof.MlKem.X86.Sample.Bs s₀) (3 * t + 2)).isLt
    rw [BitVec.toNat_add, rotr_small _ (by decide) (by decide) (by rw [toNat_byte32]; omega), toNat_shr,
      toNat_byte32, toNat_byte32, Nat.mod_eq_of_lt (by omega), VG.Proof.MlKem.X86.Sample.d₂]
    omega
  have hl := h.len
  refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ebp], h.len,
    by simp [h.edi], by simp [h.ecx], h.coef⟩, ?_⟩, ?_, ?_⟩
  · exact eq_ofNat_of_toNat x1
  · exact eq_ofNat_of_toNat x0
  · simp only [VG.X86.eval, h.ecx, toNat_ofNat32 (show (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) t).length < 2 ^ 32 by omega)]
    rfl

theorem chunk_piece (t : Nat) (ht : t < 280) :
    Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub (fun s₀ s => VG.Proof.MlKem.X86.Sample.Loop s₀ t (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) t) s) (fun s₀ s => VG.Proof.MlKem.X86.Sample.Mid s₀ t (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) t) s ∧
      s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MlKem.X86.Sample.d₁ (VG.Proof.MlKem.X86.Sample.Bs s₀) t) ∧
      VG.X86.eval .b s = some (decide ((VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) t).length < 256))) (.block smpChunk) :=
  Piece.taint [.esi] (fun s₀ s hp h => VG.Proof.MlKem.X86.Sample.chunk_ok hp ht h)
    (fun s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esi, h'.esi, hq.2.2.2.2]) (by taint_decide)

/-! ## Accepting a candidate -/

theorem cv_append (L : List Zq) (x : Zq) {i : Nat} (hi : i < L.length) : VG.Proof.MlKem.X86.Sample.cv (L ++ [x]) i = VG.Proof.MlKem.X86.Sample.cv L i := by
  simp only [VG.Proof.MlKem.X86.Sample.cv, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem cv_last (L : List Zq) {v : Nat} (hv : v < q) : VG.Proof.MlKem.X86.Sample.cv (L ++ [ofNat v]) L.length = BitVec.ofNat 32 v := by
  simp only [VG.Proof.MlKem.X86.Sample.cv, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some, val_ofNat, Nat.mod_eq_of_lt hv]

theorem store_ok {s₀ : State} (hp : VG.Proof.MlKem.X86.Sample.Pre s₀) {t : Nat} {L : List Zq} {r : Reg} {v : Nat} (hv : v < q)
    (hl : L.length < 256) {s : State} (h : VG.Proof.MlKem.X86.Sample.Mid s₀ t L s) (hrv : s.gpr r = BitVec.ofNat 32 v) :
    WP isa (.block [.store (at_ .edi 0) r, .alu .add .edi (.imm 4), .alu .add .ecx (.imm 1)]) s
      fun s' => VG.Proof.MlKem.X86.Sample.Mid s₀ t (L ++ [ofNat v]) s' := by
  have ha := hp.a_fit
  have hn : L.length < VG.Spec.MlKem.n := by rw [n_eq]; exact hl
  have ea : (VG.Proof.MlKem.X86.Sample.aP s₀ + BitVec.ofNat 32 (4 * L.length) + BitVec.ofNat 32 0).setWidth 64 =
      coeffAddr (VG.Proof.MlKem.X86.Sample.aA s₀) L.length := by
    rw [ea_add (by omega)]; rfl
  have hin : InRegions s.wr (coeffAddr (VG.Proof.MlKem.X86.Sample.aA s₀) L.length) 4 :=
    ⟨polyRegion (VG.Proof.MlKem.X86.Sample.aA s₀), by rw [h.wr, P0_wr, hp.wr]; simp, coeff_contains _ hn⟩
  have fa : Frame [polyRegion (VG.Proof.MlKem.X86.Sample.aA s₀)] s.mem (s.mem.writeW (coeffAddr (VG.Proof.MlKem.X86.Sample.aA s₀) L.length) (BitVec.ofNat 32 v)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hn)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some, h.edi, ea, hin,
    hrv, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame.writeW (r := polyRegion (VG.Proof.MlKem.X86.Sample.aA s₀)) (by simp) _
    (coeff_contains _ hn)⟩, fun p hp' => ?_, by simp [h.esi], by simp [h.ebp],
    (by simp only [List.length_append, List.length_singleton]; omega), ?_, ?_, fun i hi => ?_⟩, by simp [h.ebx]⟩
  · exact (fa.bytes (R := ⟨VG.Proof.MlKem.X86.Sample.sA s₀, 840⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.a_s.symm.sub_left (Region.sub_prefix (by decide))) (show 840 ≤ 2 ^ 64 by decide) hp').trans (h.out p hp')
  · simp only [ite_true, List.length_append, List.length_singleton]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx, List.length_append, List.length_singleton]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases e : i < L.length
    · rw [coeffAt_writeW_ne _ _ (by rw [n_eq]; omega) hn (by omega), VG.Proof.MlKem.X86.Sample.cv_append _ _ e]; exact h.coef i e
    · rw [show i = L.length by omega, coeffAt_writeW_self, VG.Proof.MlKem.X86.Sample.cv_last _ hv]

/-- Accepting the candidate `v` in `r`: the coefficients `L` become `L' = acc L v`. -/
theorem accept_piece (t : Nat) (r : Reg) {A : State → State → Prop} (X : State → Prop)
    (L L' : List Byte → List Zq) (v : List Byte → Nat)
    (hA : ∀ s₀ s, VG.Proof.MlKem.X86.Sample.Pre s₀ → A s₀ s → VG.Proof.MlKem.X86.Sample.Mid s₀ t (L (VG.Proof.MlKem.X86.Sample.Bs s₀)) s ∧ s.gpr r = BitVec.ofNat 32 (v (VG.Proof.MlKem.X86.Sample.Bs s₀)) ∧
      v (VG.Proof.MlKem.X86.Sample.Bs s₀) < 2 ^ 12 ∧ (L (VG.Proof.MlKem.X86.Sample.Bs s₀)).length < 256 ∧ VG.Proof.MlKem.X86.Sample.acc (L (VG.Proof.MlKem.X86.Sample.Bs s₀)) (v (VG.Proof.MlKem.X86.Sample.Bs s₀)) = L' (VG.Proof.MlKem.X86.Sample.Bs s₀) ∧ X s₀)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr []) (.block [.alu .cmp r (.imm Q)]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr [.edi])
      (.block [.store (at_ .edi 0) r, .alu .add .edi (.imm 4), .alu .add .ecx (.imm 1)]) h₂).isSome = true) :
    Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub A (fun s₀ s => VG.Proof.MlKem.X86.Sample.Mid s₀ t (L' (VG.Proof.MlKem.X86.Sample.Bs s₀)) s ∧ X s₀) (smpAccept r) := by
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlKem.X86.Sample.Mid s₀ t (L (VG.Proof.MlKem.X86.Sample.Bs s₀)) s ∧ s.gpr r = BitVec.ofNat 32 (v (VG.Proof.MlKem.X86.Sample.Bs s₀)) ∧
      (L (VG.Proof.MlKem.X86.Sample.Bs s₀)).length < 256 ∧ VG.Proof.MlKem.X86.Sample.acc (L (VG.Proof.MlKem.X86.Sample.Bs s₀)) (v (VG.Proof.MlKem.X86.Sample.Bs s₀)) = L' (VG.Proof.MlKem.X86.Sample.Bs s₀) ∧ X s₀ ∧
      VG.X86.eval .b s = some (decide (v (VG.Proof.MlKem.X86.Sample.Bs s₀) < q))) ?_
    (Piece.ite (fun s₀ => decide (v (VG.Proof.MlKem.X86.Sample.Bs s₀) < q)) (fun _ _ _ h => h.2.2.2.2.2)
      (fun s₀ s₀' _ _ hq => by rw [hq.2.1]) ?_ ?_)
  · refine Piece.taint [] (fun s₀ s hp ha => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) t₁
    obtain ⟨h, hv, hv', hl, he, hx⟩ := hA s₀ s hp ha
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨h.flags rfl rfl rfl rfl, hv, hl, he, hx, ?_⟩
    simp only [VG.X86.eval, hv, toNat_ofNat32 (show v (VG.Proof.MlKem.X86.Sample.Bs s₀) < 2 ^ 32 by omega)]
    rfl
  · refine Piece.taint [.edi] (fun s₀ s hp ⟨⟨h, hv, hl, he, hx, _⟩, hb⟩ => ?_)
      (fun s₀ s₀' s s' _ _ hq ⟨⟨h, _⟩, _⟩ ⟨⟨h', _⟩, _⟩ r hr => ?_) t₂
    · have hq : v (VG.Proof.MlKem.X86.Sample.Bs s₀) < q := of_decide_eq_true hb
      rw [VG.Proof.MlKem.X86.Sample.acc, ite_eq_left hq] at he
      exact (VG.Proof.MlKem.X86.Sample.store_ok hp hq hl h hv).mono fun s' h' => ⟨he ▸ h', hx⟩
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.edi, h'.edi, hq.2.2.2.1, hq.2.1]
  · refine Piece.taint [] (fun s₀ s hp ⟨⟨h, _, _, he, hx, _⟩, hb⟩ => ?_)
      (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
    have hq : ¬ v (VG.Proof.MlKem.X86.Sample.Bs s₀) < q := of_decide_eq_false hb
    rw [VG.Proof.MlKem.X86.Sample.acc, ite_eq_right hq] at he
    exact WP.block_nil_iff.mpr ⟨he ▸ h, hx⟩

theorem cmp_piece (t : Nat) (X : State → Prop) (L : List Byte → List Zq) :
    Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub (fun s₀ s => VG.Proof.MlKem.X86.Sample.Mid s₀ t (L (VG.Proof.MlKem.X86.Sample.Bs s₀)) s ∧ X s₀)
      (fun s₀ s => (VG.Proof.MlKem.X86.Sample.Mid s₀ t (L (VG.Proof.MlKem.X86.Sample.Bs s₀)) s ∧ X s₀) ∧ VG.X86.eval .b s = some (decide ((L (VG.Proof.MlKem.X86.Sample.Bs s₀)).length < 256)))
      (.block [.alu .cmp .ecx (.imm 256)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, hx⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hl := h.len
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.flags rfl rfl rfl rfl, hx⟩, ?_⟩
  simp only [VG.X86.eval, h.ecx, toNat_ofNat32 (show (L (VG.Proof.MlKem.X86.Sample.Bs s₀)).length < 2 ^ 32 by omega)]
  rfl

theorem end_ok {s₀ : State} {t : Nat} (ht : t < 280) {L : List Zq} {s : State} (h : VG.Proof.MlKem.X86.Sample.Mid s₀ t L s) :
    WP isa (.block [.alu .add .esi (.imm 3), .alu .sub .ebp (.imm 1)]) s
      fun s' => VG.Proof.MlKem.X86.Sample.Loop s₀ (t + 1) L s' ∧ VG.X86.eval .ne s' = some (decide (t + 1 < 280)) := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, ?_, ?_, h.len, by simp [h.edi], by simp [h.ecx],
    h.coef⟩, ?_⟩
  · simp only [ite_true, h.esi]
    rw [show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ebp]
    exact cnt_next ht
  · simp only [VG.X86.eval, h.ebp]
    exact cnt_ne ht (by omega)

theorem nil_piece {A B : State → State → Prop} (h : ∀ s₀ s, VG.Proof.MlKem.X86.Sample.Pre s₀ → A s₀ s → B s₀ s) :
    Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub A B (.block []) :=
  Piece.taint [] (fun s₀ s hp ha => WP.block_nil_iff.mpr (h s₀ s hp ha))
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)

/-! ## An iteration, and the loop -/

theorem body_piece (t : Nat) (ht : t < 280) :
    Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub (fun s₀ s => VG.Proof.MlKem.X86.Sample.Loop s₀ t (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) t) s)
      (fun s₀ s => VG.Proof.MlKem.X86.Sample.Loop s₀ (t + 1) (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) (t + 1)) s ∧ VG.X86.eval .ne s = some (decide (t + 1 < 280)))
      smpBody := by
  refine Piece.seq (VG.Proof.MlKem.X86.Sample.chunk_piece t ht) (Piece.seq (B := fun s₀ s => VG.Proof.MlKem.X86.Sample.Mid s₀ t (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) (t + 1)) s) ?_
    (Piece.taint [] (fun s₀ s _ h => VG.Proof.MlKem.X86.Sample.end_ok ht h) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)))
  refine Piece.ite (fun s₀ => decide ((VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) t).length < 256)) (fun _ _ _ h => h.2.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.2.1]) ?_ ?_
  · refine Piece.seq (VG.Proof.MlKem.X86.Sample.accept_piece t .eax (fun s₀ => (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) t).length < 256) (fun B => VG.Proof.MlKem.X86.Sample.LA B t)
      (fun B => VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.LA B t) (VG.Proof.MlKem.X86.Sample.d₁ B t)) (fun B => VG.Proof.MlKem.X86.Sample.d₁ B t)
      (fun s₀ s _ ⟨⟨h, he, _⟩, hb⟩ => ⟨h, he, VG.Proof.MlKem.X86.Sample.d₁_lt _ _, of_decide_eq_true hb, rfl, of_decide_eq_true hb⟩)
      (by taint_decide) (by taint_decide)) ?_
    refine Piece.seq (VG.Proof.MlKem.X86.Sample.cmp_piece t _ (fun B => VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.LA B t) (VG.Proof.MlKem.X86.Sample.d₁ B t))) ?_
    refine Piece.ite (fun s₀ => decide ((VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) t) (VG.Proof.MlKem.X86.Sample.d₁ (VG.Proof.MlKem.X86.Sample.Bs s₀) t)).length < 256)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by rw [hq.2.1]) ?_ ?_
    · exact (VG.Proof.MlKem.X86.Sample.accept_piece t .ebx (fun _ => True) (fun B => VG.Proof.MlKem.X86.Sample.acc (VG.Proof.MlKem.X86.Sample.LA B t) (VG.Proof.MlKem.X86.Sample.d₁ B t)) (fun B => VG.Proof.MlKem.X86.Sample.LA B (t + 1))
        (fun B => VG.Proof.MlKem.X86.Sample.d₂ B t) (fun s₀ s _ ⟨⟨⟨h, hx⟩, _⟩, hb⟩ =>
          ⟨h, h.ebx, VG.Proof.MlKem.X86.Sample.d₂_lt _ _, of_decide_eq_true hb, VG.Proof.MlKem.X86.Sample.LA_then hx (of_decide_eq_true hb), trivial⟩)
        (by taint_decide) (by taint_decide)).mono (fun _ _ _ h => h) fun _ _ _ h => h.1
    · exact VG.Proof.MlKem.X86.Sample.nil_piece fun s₀ s _ ⟨⟨⟨h, hx⟩, _⟩, hb⟩ => VG.Proof.MlKem.X86.Sample.LA_then' hx (of_decide_eq_false hb) ▸ h
  · exact VG.Proof.MlKem.X86.Sample.nil_piece fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => VG.Proof.MlKem.X86.Sample.LA_else (of_decide_eq_false hb) ▸ h

theorem loop_piece : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub (fun s₀ s => VG.Proof.MlKem.X86.Sample.Loop s₀ 0 (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 0) s)
    (fun s₀ s => VG.Proof.MlKem.X86.Sample.Loop s₀ 280 (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280) s) (.loop smpBody .ne) :=
  Piece.loop (fun t s₀ s => VG.Proof.MlKem.X86.Sample.Loop s₀ t (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) t) s) (by decide) fun t ht => VG.Proof.MlKem.X86.Sample.body_piece t ht

/-- The end: 1 in `eax` if there are 256 coefficients, 0 if fewer. -/
structure Fin (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Sample.Loop s₀ 280 (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280) s where
  eax : s.gpr .eax = BitVec.ofNat 32 ((VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280).length / 256)

theorem fin_piece : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub (fun s₀ s => VG.Proof.MlKem.X86.Sample.Loop s₀ 280 (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280) s) VG.Proof.MlKem.X86.Sample.Fin (.block smpEnd) := by
  refine Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hl := h.len
  refine wp_movr (wp_shr (by decide) (by decide) fun s' o e => WP.block_nil_iff.mpr ?_)
  have g : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r := fun r hr => by
    rw [o.gpr r (by simp [hr])]; simp [State.setReg, hr]
  refine ⟨⟨⟨by rw [g _ (by decide), h.esp], by rw [o.rd]; exact h.rd, by rw [o.wr]; exact h.wr, by rw [o.mem]; exact h.frame⟩,
    by rw [o.mem]; exact h.out, by rw [g _ (by decide), h.esi], by rw [g _ (by decide), h.ebp], h.len,
    by rw [g _ (by decide), h.edi], by rw [g _ (by decide), h.ecx], by rw [o.mem]; exact h.coef⟩, ?_⟩
  rw [e]
  simp only [State.setReg, ite_true, h.ecx]
  exact eq_ofNat_of_toNat (by rw [toNat_shr, toNat_ofNat32 (show (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280).length < 2 ^ 32 by omega)])

end VG.Proof.MlKem.X86.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Sample`. -/
section

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_sample_ntt`

The body is the SHAKE128 output of the seed at `scratch` (`SampleSetup.lean`,
`SampleCalls.lean`), then the 280 iterations of the loop (`SampleLoop.lean`),
which leave `sampleAfter [] (xofByte B) 280` at `a` and return whether it has
256 coefficients; `sampleNTT_of_full`, `sampleNTT_none` and `outcome_of_min`
(`Proof/MlKem/KPke.lean`) give the contract. Two runs with the same pointers
and seed leak the same (`Pub`): the contract lets the function leak the seed.
-/

namespace VG.Proof.MlKem.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem main_piece : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlKem.X86.Sample.Fin
    (.seq (.block [.mov .esi (.mem (at_ .esp 28))]) <|
      .seq (zeroSt smpSt) <|
      .seq (.block smpAbsorbArgs) <|
      .seq (callWith [.edi, .ebp, .ebx, .edx, .ecx, .eax] "vg_keccak_absorb_scratch" Impl.Sha3.X86.Stream.absorb) <|
      .seq (.block smpPadArgs) <|
      .seq (callWith [.edi, .ebx, .edx, .ecx, .eax] "vg_keccak_pad_scratch" Impl.Sha3.X86.Stream.pad) <|
      .seq (.block smpSqueezeArgs) <|
      .seq (callWith [.edi, .ebp, .ebx, .edx, .ecx, .eax] "vg_keccak_squeeze_scratch" Impl.Sha3.X86.Stream.squeeze) <|
      .seq (.block smpLoopInit) <|
      .seq (.loop smpBody .ne) (.block smpEnd)) :=
  Piece.seq VG.Proof.MlKem.X86.Sample.ld_piece <| Piece.seq VG.Proof.MlKem.X86.Sample.zero_piece <| Piece.seq VG.Proof.MlKem.X86.Sample.absArgs_piece <| Piece.seq VG.Proof.MlKem.X86.Sample.absorb_call <|
    Piece.seq VG.Proof.MlKem.X86.Sample.padArgs_piece <| Piece.seq VG.Proof.MlKem.X86.Sample.pad_call <| Piece.seq VG.Proof.MlKem.X86.Sample.sqArgs_piece <| Piece.seq VG.Proof.MlKem.X86.Sample.squeeze_call <|
    Piece.seq VG.Proof.MlKem.X86.Sample.linit_piece <| Piece.seq VG.Proof.MlKem.X86.Sample.loop_piece VG.Proof.MlKem.X86.Sample.fin_piece

theorem piece : Piece VG.Proof.MlKem.X86.Sample.Pre VG.Proof.MlKem.X86.Sample.Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlKem.X86.Sample.Fin s₀) s₀ s')
    Impl.MlKem.X86.sampleNTT :=
  Piece.leaf VG.Proof.MlKem.X86.Sample.W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨by have := hp.sp; omega, by have := hp.sp'; omega⟩)
    (fun _ hp => hp.hW) (fun _ _ _ _ hq => hq.1)
    (main_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- The coefficients at `a`, when there are 256. -/
theorem poly_eq {s₀ s : State} (h : VG.Proof.MlKem.X86.Sample.Loop s₀ 280 (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280) s) (hl : (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280).length = 256) :
    Reduced s.mem (VG.Proof.MlKem.X86.Sample.aA s₀) ∧ polyAt s.mem (VG.Proof.MlKem.X86.Sample.aA s₀) = toPoly (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280) := by
  have hc : ∀ i < VG.Spec.MlKem.n, coeffAt s.mem (VG.Proof.MlKem.X86.Sample.aA s₀) i = VG.Proof.MlKem.X86.Sample.cv (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280) i := fun i hi =>
    h.coef i (by rw [hl]; rw [n_eq] at hi; exact hi)
  have hv : ∀ i < VG.Spec.MlKem.n, (coeffAt s.mem (VG.Proof.MlKem.X86.Sample.aA s₀) i).toNat = ((VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280).getD i 0).val := fun i hi => by
    rw [hc i hi, VG.Proof.MlKem.X86.Sample.cv, toNat_ofNat32 (by have := ((VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280).getD i 0).isLt; have := q_eq; omega)]
  refine ⟨fun i hi => by rw [hv i hi]; exact ((VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280).getD i 0).isLt, ?_⟩
  apply Vector.ext
  intro i hi
  simp only [polyAt, toPoly, Vector.getElem_ofFn]
  rw [hv i hi, ofNat_val]

/-- Memory with the arguments `0`, `0x100` and `0x1000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 1 else if a = 0x500d then 0x10 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.sampleNTT (sampleNTTContract X86.abi 56) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => ?_).mono
    (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · sig_pub [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := h
    exact ⟨e₁, map_toNat_inj e₂, e₃, e₄, e₅⟩
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have hl := hfin.len
    by_cases e : (VG.Proof.MlKem.X86.Sample.LA (VG.Proof.MlKem.X86.Sample.Bs s₀) 280).length = 256
    · obtain ⟨hr, hp⟩ := VG.Proof.MlKem.X86.Sample.poly_eq hfin.toLoop e
      rw [e]
      refine ⟨fun _ => hr, outcome_of_min (.inl ⟨rfl, ?_⟩)⟩
      rw [hp]
      exact sampleNTT_of_full (Nat.le_refl _) (by rw [n_eq]; exact e)
    · rw [Nat.div_eq_of_lt (by omega)]
      refine ⟨fun h => absurd (congrArg BitVec.toNat h) (by show ¬ (0 = 1); decide), outcome_of_min (.inr ⟨rfl, ?_⟩)⟩
      exact sampleNTT_none (by rw [n_eq]; exact e)
  · let st := VG.Proof.MlKem.X86.satState VG.Proof.MlKem.X86.Sample.satMem [⟨0, 34⟩] [⟨0x100, 1024⟩, ⟨0x1000, 2048⟩, ⟨0x5004, 12⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlKem.X86.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Top`. -/
section

/-!
# ML-KEM on x86 (32-bit): the setting of the top-level functions

A top-level function takes buffers as arguments (`Lay`: each one's length, and
whether it is written), one of which (`sc`) is its working space `scratch`;
its precondition (`TPre`, which its contract implies) says where they are. It
saves its caller's registers in a frame of 16 bytes (`leaf`), keeps `esi =
scratch`, and calls the primitives and the Keccak functions, whose calls use
the `stk - 16` bytes of stack below the frame.

Buffers are named by an argument and an offset (`Buf`), so that whether
two are disjoint (`Buf.sep`), and whether one lies in its argument
(`Buf.ok`), are computed (`decide`) from the numbers. `Ctx` is what holds
throughout the body: `esp`, `esi`, the permissions, and memory changed only
in the written arguments and the calls' stack (`W`).
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.Sha3.X86 (reg32)

/-- The layout of a top-level function: its arguments' lengths and whether
each is written; which one is `scratch`; and the stack its contract gives. -/
structure Lay where
  args : List (Nat × Bool)
  sc : Nat
  stk : Nat

namespace Lay
variable (Y : VG.Proof.MlKem.X86.Top.Lay)
def alen (i : Nat) : Nat := (Y.args.getD i (0, false)).1
def awr (i : Nat) : Bool := (Y.args.getD i (0, false)).2
def n : Nat := Y.args.length

/-- `b` is within its argument, and not empty. -/
def ok (b : Buf) : Bool := decide (b.arg < Y.n) && decide (0 < b.len) && decide (b.off + b.len ≤ Y.alen b.arg)
/-- `b` is within an argument that is written. -/
def okW (b : Buf) : Bool := Y.ok b && Y.awr b.arg
/-- `b` and `c` do not overlap, or are in arguments one of which is written
(which the precondition makes disjoint). -/
def sep (b c : Buf) : Bool :=
  if b.arg = c.arg then decide (b.off + b.len ≤ c.off) || decide (c.off + c.len ≤ b.off)
  else Y.awr b.arg || Y.awr c.arg
end Lay

section
variable (Y : VG.Proof.MlKem.X86.Top.Lay) (s₀ : State)
abbrev argR (i : Nat) : Region := ⟨(arg s₀ i).setWidth 64, Y.alen i⟩
abbrev gR : Region := ⟨argAddr s₀ 0, 4 * Y.n⟩
/-- `esp` in the body. -/
abbrev E1 : BitVec 32 := (P0 s₀).gpr .esp
/-- The stack the calls use. -/
abbrev cR : Region := below (VG.Proof.MlKem.X86.Top.E1 s₀) (Y.stk - 16)
/-- What the body may change: the written arguments and the calls' stack. -/
def W : List Region := ((List.range Y.n).filter Y.awr).map (VG.Proof.MlKem.X86.Top.argR Y s₀) ++ [VG.Proof.MlKem.X86.Top.cR Y s₀]
end

section
variable (s₀ : State) (b : Buf)
/-- The address of `b`. -/
abbrev _root_.VG.Impl.MlKem.X86.Buf.ptr : BitVec 32 := VG.X86.arg s₀ b.arg + BitVec.ofNat 32 b.off
abbrev _root_.VG.Impl.MlKem.X86.Buf.addr : Addr := (b.ptr s₀).setWidth 64
abbrev _root_.VG.Impl.MlKem.X86.Buf.rgn : Region := reg32 (b.ptr s₀) b.len
end

structure TPre (Y : VG.Proof.MlKem.X86.Top.Lay) (s₀ : State) : Prop where
  sp : Y.stk ≤ (E0 s₀).toNat
  sp16 : 16 ≤ Y.stk
  sp' : (E0 s₀).toNat + 4 + 4 * Y.n ≤ 2 ^ 32
  rd : ∀ i < Y.n, Y.awr i = false → VG.Proof.MlKem.X86.Top.argR Y s₀ i ∈ s₀.rd
  wr : ∀ i < Y.n, Y.awr i = true → VG.Proof.MlKem.X86.Top.argR Y s₀ i ∈ s₀.wr
  gwr : VG.Proof.MlKem.X86.Top.gR Y s₀ ∈ s₀.rd ++ s₀.wr
  disj : ∀ i < Y.n, ∀ j < Y.n, i ≠ j → (Y.awr i || Y.awr j) = true → (VG.Proof.MlKem.X86.Top.argR Y s₀ i).Disjoint (VG.Proof.MlKem.X86.Top.argR Y s₀ j)
  g_disj : ∀ i < Y.n, (VG.Proof.MlKem.X86.Top.gR Y s₀).Disjoint (VG.Proof.MlKem.X86.Top.argR Y s₀ i)
  ret : ∀ i < Y.n, (VG.Proof.MlKem.X86.retR s₀).Disjoint (VG.Proof.MlKem.X86.Top.argR Y s₀ i)
  stk_a : ∀ i < Y.n, (below (E0 s₀) Y.stk).Disjoint (VG.Proof.MlKem.X86.Top.argR Y s₀ i)
  stk_g : (below (E0 s₀) Y.stk).Disjoint (VG.Proof.MlKem.X86.Top.gR Y s₀)
  fit : ∀ i < Y.n, (arg s₀ i).toNat + Y.alen i ≤ 2 ^ 32
  sc_lt : Y.sc < Y.n

/-- Two runs agree on `esp`, the arguments and what `lk` says the function may leak. -/
def TPub (Y : VG.Proof.MlKem.X86.Top.Lay) (lk : State → List Byte) (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ (∀ i < Y.n, arg s₀ i = arg s₀' i) ∧ lk s₀ = lk s₀'

theorem TPub.E1 {Y : VG.Proof.MlKem.X86.Top.Lay} {lk : State → List Byte} {s₀ s₀' : State} (hq : VG.Proof.MlKem.X86.Top.TPub Y lk s₀ s₀') :
    VG.Proof.MlKem.X86.Top.E1 s₀ = VG.Proof.MlKem.X86.Top.E1 s₀' := by
  simp only [P0_esp, hq.1]

theorem TPub.sc {Y : VG.Proof.MlKem.X86.Top.Lay} {lk : State → List Byte} {s₀ s₀' : State} (hq : VG.Proof.MlKem.X86.Top.TPub Y lk s₀ s₀') (hp : VG.Proof.MlKem.X86.Top.TPre Y s₀) :
    arg s₀ Y.sc = arg s₀' Y.sc := hq.2.1 _ hp.sc_lt

theorem TPub.ptr {Y : VG.Proof.MlKem.X86.Top.Lay} {lk : State → List Byte} {s₀ s₀' : State} (hq : VG.Proof.MlKem.X86.Top.TPub Y lk s₀ s₀') {b : Buf}
    (hb : Y.ok b = true) : b.ptr s₀ = b.ptr s₀' := by
  simp only [Lay.ok, Bool.and_eq_true, decide_eq_true_eq] at hb
  simp only [Buf.ptr, hq.2.1 _ hb.1.1]

/-! ## Stack geometry -/

theorem below_adj {sp : BitVec 32} {a b : Nat} (h : a + b ≤ sp.toNat) :
    (below sp a).Disjoint (below (sp - BitVec.ofNat 32 a) b) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have hk : b ≤ (sp - BitVec.ofNat 32 a).toNat := by rw [sub_toNat (by omega)]; omega
  rw [Taint.sub_setWidth (by omega)] at h₁
  rw [Taint.sub_setWidth hk, Taint.sub_setWidth (by omega)] at h₂
  have := sp.isLt
  have hE : (sp.setWidth 64).toNat = sp.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize sp.setWidth 64 = E at *
  bv_omega

theorem ret_below {sp : BitVec 32} {n : Nat} (h : n ≤ sp.toNat) :
    (⟨sp.setWidth 64, 4⟩ : Region).Disjoint (below sp n) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth h] at h₂
  have := sp.isLt
  have hE : (sp.setWidth 64).toNat = sp.toNat := by
    simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  generalize sp.setWidth 64 = E at *
  bv_omega

theorem E1_nat (s₀ : State) (h : 16 ≤ (E0 s₀).toNat) : (VG.Proof.MlKem.X86.Top.E1 s₀).toNat = (E0 s₀).toNat - 16 := by
  rw [VG.Proof.MlKem.X86.Top.E1, P0_esp]; exact sub_toNat (k := 16) h

theorem E1_eq (s₀ : State) : VG.Proof.MlKem.X86.Top.E1 s₀ = E0 s₀ - BitVec.ofNat 32 16 := P0_esp s₀

theorem toNat_off {x : BitVec 32} {o : Nat} (h : x.toNat + o < 2 ^ 32) :
    (x + BitVec.ofNat 32 o).toNat = x.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt h]

namespace TPre
variable {Y : VG.Proof.MlKem.X86.Top.Lay} {s₀ : State} (hp : VG.Proof.MlKem.X86.Top.TPre Y s₀)
include hp

theorem E0_big : 16 ≤ (E0 s₀).toNat := Nat.le_trans hp.sp16 hp.sp

theorem stk_eq : (⟨(E0 s₀).setWidth 64 - BitVec.ofNat 64 Y.stk, Y.stk⟩ : Region) = below (E0 s₀) Y.stk := by
  simp only [below]; rw [Taint.sub_setWidth hp.sp]

theorem frame_sub : Region.Sub (frameR s₀) (below (E0 s₀) Y.stk) := below_sub hp.sp16 hp.sp

theorem c_sub : Region.Sub (VG.Proof.MlKem.X86.Top.cR Y s₀) (below (E0 s₀) Y.stk) := by
  rw [VG.Proof.MlKem.X86.Top.cR, VG.Proof.MlKem.X86.Top.E1_eq]
  exact below_inner (by have := hp.sp16; omega) hp.sp

theorem frame_c : (frameR s₀).Disjoint (VG.Proof.MlKem.X86.Top.cR Y s₀) := by
  rw [VG.Proof.MlKem.X86.Top.cR, VG.Proof.MlKem.X86.Top.E1_eq]; exact VG.Proof.MlKem.X86.Top.below_adj (by have := hp.sp; have := hp.sp16; omega)

theorem ret_c : (VG.Proof.MlKem.X86.retR s₀).Disjoint (VG.Proof.MlKem.X86.Top.cR Y s₀) := (VG.Proof.MlKem.X86.Top.ret_below hp.sp).sub_right hp.c_sub

theorem fr16 : (⟨(E0 s₀).setWidth 64 - 16#64, 16⟩ : Region) = frameR s₀ := by
  simp only [frameR, below]; rw [Taint.sub_setWidth hp.E0_big]

omit hp in
theorem mem_W {r : Region} (h : r ∈ VG.Proof.MlKem.X86.Top.W Y s₀) : (∃ i < Y.n, Y.awr i = true ∧ r = VG.Proof.MlKem.X86.Top.argR Y s₀ i) ∨ r = VG.Proof.MlKem.X86.Top.cR Y s₀ := by
  simp only [VG.Proof.MlKem.X86.Top.W, List.mem_append, List.mem_map, List.mem_filter, List.mem_range, List.mem_singleton] at h
  rcases h with ⟨i, ⟨hi, hw⟩, rfl⟩ | rfl
  · exact .inl ⟨i, hi, hw, rfl⟩
  · exact .inr rfl

theorem hW : ∀ r ∈ VG.Proof.MlKem.X86.Top.W Y s₀, (frameR s₀).Disjoint r ∧ (VG.Proof.MlKem.X86.retR s₀).Disjoint r := by
  intro r hr
  rcases VG.Proof.MlKem.X86.Top.TPre.mem_W hr with ⟨i, hi, _, rfl⟩ | rfl
  · exact ⟨(hp.stk_a i hi).sub_left hp.frame_sub, hp.ret i hi⟩
  · exact ⟨hp.frame_c, hp.ret_c⟩

omit hp in
theorem argW {i : Nat} (hi : i < Y.n) (hw : Y.awr i = true) : VG.Proof.MlKem.X86.Top.argR Y s₀ i ∈ VG.Proof.MlKem.X86.Top.W Y s₀ := by
  simp only [VG.Proof.MlKem.X86.Top.W, List.mem_append, List.mem_map, List.mem_filter, List.mem_range]
  exact .inl ⟨i, ⟨hi, hw⟩, rfl⟩

omit hp in
theorem cW : VG.Proof.MlKem.X86.Top.cR Y s₀ ∈ VG.Proof.MlKem.X86.Top.W Y s₀ := by simp [VG.Proof.MlKem.X86.Top.W]

/-- A buffer read-only on entry is disjoint from everything the body changes. -/
theorem roW {i : Nat} (hi : i < Y.n) (hw : Y.awr i = false) : ∀ r ∈ VG.Proof.MlKem.X86.Top.W Y s₀, (VG.Proof.MlKem.X86.Top.argR Y s₀ i).Disjoint r := by
  intro r hr
  rcases VG.Proof.MlKem.X86.Top.TPre.mem_W hr with ⟨j, hj, hwj, rfl⟩ | rfl
  · exact hp.disj i hi j hj (by rintro rfl; rw [hw] at hwj; cases hwj) (by rw [hwj]; simp)
  · exact ((hp.stk_a i hi).sub_left hp.c_sub).symm

theorem gW : ∀ r ∈ VG.Proof.MlKem.X86.Top.W Y s₀, (VG.Proof.MlKem.X86.Top.gR Y s₀).Disjoint r := by
  intro r hr
  rcases VG.Proof.MlKem.X86.Top.TPre.mem_W hr with ⟨j, hj, _, rfl⟩ | rfl
  · exact hp.g_disj j hj
  · exact (hp.stk_g.sub_left hp.c_sub).symm

end TPre

/-! ## Buffers -/

/-- Two parts of a region at a 32-bit pointer that do not overlap. -/
theorem disj_at {x : BitVec 32} {len a b n k : Nat} (ha : a + n ≤ len) (hb : b + k ≤ len)
    (hx : x.toNat + len ≤ 2 ^ 32) (h : a + n ≤ b ∨ b + k ≤ a) :
    (⟨x.setWidth 64 + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨x.setWidth 64 + BitVec.ofNat 64 b, k⟩ :=
  fun y h₁ h₂ => sep_at ha hb hx h y (by simp only [Region.Contains] at h₁; omega)
    (by simp only [Region.Contains] at h₂; omega)

theorem Lay.ok_iff {Y : VG.Proof.MlKem.X86.Top.Lay} {b : Buf} :
    Y.ok b = true ↔ b.arg < Y.n ∧ 0 < b.len ∧ b.off + b.len ≤ Y.alen b.arg := by
  simp [Lay.ok, and_assoc]

theorem Lay.okW_iff {Y : VG.Proof.MlKem.X86.Top.Lay} {b : Buf} : Y.okW b = true ↔ Y.ok b = true ∧ Y.awr b.arg = true := by
  simp [Lay.okW]

namespace Buf
variable {Y : VG.Proof.MlKem.X86.Top.Lay} {s₀ : State} (hp : VG.Proof.MlKem.X86.Top.TPre Y s₀) {b : Buf} (hb : Y.ok b = true)
include hp hb

theorem ptr_nat : (b.ptr s₀).toNat = (X86.arg s₀ b.arg).toNat + b.off := by
  obtain ⟨h₁, h₂, h₃⟩ := Lay.ok_iff.mp hb
  have := hp.fit _ h₁
  exact VG.Proof.MlKem.X86.Top.toNat_off (by omega)

theorem fit : (b.ptr s₀).toNat + b.len ≤ 2 ^ 32 := by
  obtain ⟨h₁, h₂, h₃⟩ := Lay.ok_iff.mp hb
  have := hp.fit _ h₁
  rw [VG.Proof.MlKem.X86.Top.Buf.ptr_nat hp hb]; omega

theorem addr_eq : b.addr s₀ = (X86.arg s₀ b.arg).setWidth 64 + BitVec.ofNat 64 b.off := by
  obtain ⟨h₁, h₂, h₃⟩ := Lay.ok_iff.mp hb
  have := hp.fit _ h₁
  exact ea_off (by omega)

theorem sub : Region.Sub (b.rgn s₀) (VG.Proof.MlKem.X86.Top.argR Y s₀ b.arg) := by
  obtain ⟨h₁, h₂, h₃⟩ := Lay.ok_iff.mp hb
  show Region.Sub ⟨b.addr s₀, b.len⟩ _
  rw [VG.Proof.MlKem.X86.Top.Buf.addr_eq hp hb]
  exact sub_of_contains (contains_at h₃ (hp.fit _ h₁))

theorem stkD {N : Nat} (hN : N + 16 ≤ Y.stk) : (below (VG.Proof.MlKem.X86.Top.E1 s₀) N).Disjoint (b.rgn s₀) := by
  obtain ⟨h₁, -, -⟩ := Lay.ok_iff.mp hb
  refine ((hp.stk_a _ h₁).sub_left ?_).sub_right (VG.Proof.MlKem.X86.Top.Buf.sub hp hb)
  rw [VG.Proof.MlKem.X86.Top.E1_eq]
  exact below_inner hN hp.sp

theorem disj {c : Buf} (hc : Y.ok c = true) (hs : Y.sep b c = true) : (b.rgn s₀).Disjoint (c.rgn s₀) := by
  obtain ⟨hb₁, hb₂, hb₃⟩ := Lay.ok_iff.mp hb
  obtain ⟨hc₁, hc₂, hc₃⟩ := Lay.ok_iff.mp hc
  unfold Lay.sep at hs
  split at hs
  · rename_i e
    show Region.Disjoint ⟨b.addr s₀, b.len⟩ ⟨c.addr s₀, c.len⟩
    rw [VG.Proof.MlKem.X86.Top.Buf.addr_eq hp hb, VG.Proof.MlKem.X86.Top.Buf.addr_eq hp hc, ← e]
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hs
    rw [e] at hb₃
    exact VG.Proof.MlKem.X86.Top.disj_at (len := Y.alen c.arg) (by omega) hc₃ (by rw [← e]; exact hp.fit _ hb₁) hs
  · rename_i e
    exact ((hp.disj _ hb₁ _ hc₁ e hs).sub_left (VG.Proof.MlKem.X86.Top.Buf.sub hp hb)).sub_right (VG.Proof.MlKem.X86.Top.Buf.sub hp hc)

theorem within {s : State} (hr : s.rd = (P0 s₀).rd) (hw : s.wr = (P0 s₀).wr) :
    VG.Proof.MlKem.X86.Within (b.rgn s₀) (s.rd ++ s.wr) := by
  obtain ⟨h₁, -, h₃⟩ := Lay.ok_iff.mp hb
  refine ⟨VG.Proof.MlKem.X86.Top.argR Y s₀ b.arg, ?_, b.off, VG.Proof.MlKem.X86.Top.Buf.addr_eq hp hb, h₃⟩
  rw [hr, hw, pushed_rd, P0_wr]
  cases e : Y.awr b.arg
  · exact List.mem_append_left _ (hp.rd _ h₁ e)
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (hp.wr _ h₁ e))

theorem withinW (hw' : Y.awr b.arg = true) {s : State} (hw : s.wr = (P0 s₀).wr) : VG.Proof.MlKem.X86.Within (b.rgn s₀) s.wr := by
  obtain ⟨h₁, -, h₃⟩ := Lay.ok_iff.mp hb
  refine ⟨VG.Proof.MlKem.X86.Top.argR Y s₀ b.arg, ?_, b.off, VG.Proof.MlKem.X86.Top.Buf.addr_eq hp hb, h₃⟩
  rw [hw, P0_wr]
  exact List.mem_cons_of_mem _ (hp.wr _ h₁ hw')

theorem inW (hw' : Y.awr b.arg = true) : ∃ r ∈ VG.Proof.MlKem.X86.Top.W Y s₀, Region.Sub (b.rgn s₀) r :=
  ⟨_, TPre.argW (Lay.ok_iff.mp hb).1 hw', VG.Proof.MlKem.X86.Top.Buf.sub hp hb⟩

theorem roW (hro : Y.awr b.arg = false) : ∀ r ∈ VG.Proof.MlKem.X86.Top.W Y s₀, (b.rgn s₀).Disjoint r :=
  fun r hr => (hp.roW (Lay.ok_iff.mp hb).1 hro r hr).sub_left (VG.Proof.MlKem.X86.Top.Buf.sub hp hb)

/-- A buffer apart from the regions a call changes. -/
theorem frD {bs : List Buf} (hbs : bs.all (fun c => Y.ok c && Y.sep b c) = true) {N : Nat}
    (hN : N + 16 ≤ Y.stk) : ∀ r ∈ bs.map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) N], (b.rgn s₀).Disjoint r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    have := List.all_eq_true.mp hbs c hc
    simp only [Bool.and_eq_true] at this
    exact VG.Proof.MlKem.X86.Top.Buf.disj hp hb this.1 this.2
  · rw [List.mem_singleton] at hr; subst hr
    exact (VG.Proof.MlKem.X86.Top.Buf.stkD hp hb hN).symm

theorem inRegW (hw' : Y.awr b.arg = true) {s : State} (hw : s.wr = (P0 s₀).wr) {o n : Nat}
    (h : o + n ≤ b.len) : InRegions s.wr (b.addr s₀ + BitVec.ofNat 64 o) n := by
  obtain ⟨h₁, -, h₃⟩ := Lay.ok_iff.mp hb
  refine ⟨VG.Proof.MlKem.X86.Top.argR Y s₀ b.arg, by rw [hw, P0_wr]; exact List.mem_cons_of_mem _ (hp.wr _ h₁ hw'), ?_⟩
  rw [VG.Proof.MlKem.X86.Top.Buf.addr_eq hp hb, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact contains_at (by omega) (hp.fit _ h₁)

theorem inRegR {s : State} (hr : s.rd = (P0 s₀).rd) (hw : s.wr = (P0 s₀).wr) {o n : Nat}
    (h : o + n ≤ b.len) : InRegions (s.rd ++ s.wr) (b.addr s₀ + BitVec.ofNat 64 o) n := by
  obtain ⟨h₁, -, h₃⟩ := Lay.ok_iff.mp hb
  refine ⟨VG.Proof.MlKem.X86.Top.argR Y s₀ b.arg, ?_, ?_⟩
  · rw [hr, hw, pushed_rd, P0_wr]
    cases e : Y.awr b.arg
    · exact List.mem_append_left _ (hp.rd _ h₁ e)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (hp.wr _ h₁ e))
  · rw [VG.Proof.MlKem.X86.Top.Buf.addr_eq hp hb, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact contains_at (by omega) (hp.fit _ h₁)

/-- The part of `b` at `o`, within its argument, for a store. -/
theorem contains (hw' : Y.awr b.arg = true) {o n : Nat} (h : o + n ≤ b.len) :
    ∃ r ∈ VG.Proof.MlKem.X86.Top.W Y s₀, r.Contains (b.addr s₀ + BitVec.ofNat 64 o) n := by
  obtain ⟨h₁, -, h₃⟩ := Lay.ok_iff.mp hb
  refine ⟨VG.Proof.MlKem.X86.Top.argR Y s₀ b.arg, TPre.argW h₁ hw', ?_⟩
  rw [VG.Proof.MlKem.X86.Top.Buf.addr_eq hp hb, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact contains_at (by omega) (hp.fit _ h₁)

omit hb in
theorem frSub {bs : List Buf} (hbs : bs.all Y.okW = true) {N : Nat} (hN : N + 16 ≤ Y.stk) :
    ∀ r ∈ bs.map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) N], ∃ r' ∈ VG.Proof.MlKem.X86.Top.W Y s₀, Region.Sub r r' := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    obtain ⟨h₁, h₂⟩ := Lay.okW_iff.mp (List.all_eq_true.mp hbs c hc)
    exact VG.Proof.MlKem.X86.Top.Buf.inW hp h₁ h₂
  · rw [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.MlKem.X86.Top.cR Y s₀, TPre.cW, below_sub (by omega) (by rw [VG.Proof.MlKem.X86.Top.E1_nat s₀ hp.E0_big]; have := hp.sp; omega)⟩

end Buf

/-! ## What holds throughout the body -/

structure Ctx (Y : VG.Proof.MlKem.X86.Top.Lay) (s₀ s : State) : Prop where
  esp : s.gpr .esp = VG.Proof.MlKem.X86.Top.E1 s₀
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = arg s₀ Y.sc
  frame : Frame (VG.Proof.MlKem.X86.Top.W Y s₀) (P0 s₀).mem s.mem

namespace Ctx
variable {Y : VG.Proof.MlKem.X86.Top.Lay} {s₀ s : State}

theorem same {s' : State} (h : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s) (e₁ : s'.gpr .esp = s.gpr .esp) (e₂ : s'.gpr .esi = s.gpr .esi)
    (e₃ : s'.rd = s.rd) (e₄ : s'.wr = s.wr) (e₅ : s'.mem = s.mem) : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' :=
  ⟨by rw [e₁, h.esp], by rw [e₃, h.rd], by rw [e₄, h.wr], by rw [e₂, h.esi], by rw [e₅]; exact h.frame⟩

/-- After a call that changes memory only within `rs`, parts of `W`. -/
theorem call {s' : State} (h : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s) (e₁ : s'.rd = s.rd) (e₂ : s'.wr = s.wr)
    (e₃ : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) {rs : List Region} (fr : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ VG.Proof.MlKem.X86.Top.W Y s₀, Region.Sub r r') : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' :=
  ⟨by rw [e₃ .esp (by simp [calleeSaved]), h.esp], by rw [e₁, h.rd], by rw [e₂, h.wr],
    by rw [e₃ .esi (by simp [calleeSaved]), h.esi], h.frame.trans (fr.sub hs)⟩

variable (hp : VG.Proof.MlKem.X86.Top.TPre Y s₀) (h : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s)
include hp h

/-- The bytes of a buffer read-only on entry. -/
theorem ro {b : Buf} (hb : Y.ok b = true) (hro : Y.awr b.arg = false) {i : Nat} (hi : i < b.len) :
    s.mem (b.addr s₀ + BitVec.ofNat 64 i) = s₀.mem (b.addr s₀ + BitVec.ofNat 64 i) := by
  have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hp.E0_big)
  rw [saveRegs_len] at hf
  obtain ⟨h₁, -, -⟩ := Lay.ok_iff.mp hb
  rw [h.frame.bytes (R := b.rgn s₀) (Buf.roW hp hb hro) (by show b.len ≤ 2 ^ 64; have := Buf.fit hp hb; omega) hi]
  exact hf.bytes (R := b.rgn s₀) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (((hp.stk_a _ h₁).sub_left hp.frame_sub).sub_right (Buf.sub hp hb)).symm)
    (by show b.len ≤ 2 ^ 64; have := Buf.fit hp hb; omega) hi

theorem roBytes {b : Buf} (hb : Y.ok b = true) (hro : Y.awr b.arg = false) :
    Spec.Sha3.bytesAt s.mem (b.addr s₀) b.len = Spec.Sha3.bytesAt s₀.mem (b.addr s₀) b.len :=
  bytesAt_congr fun _ hi => h.ro hp hb hro hi

theorem argw {i : Nat} (hi : i < Y.n) : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have fit := hp.sp'
  rw [h.frame.readW (VG.Proof.MlKem.X86.arg_contains hi fit) hp.gW (by decide)]
  exact P0_arg hp.E0_big hi fit (by rw [hp.fr16]; exact hp.stk_g.sub_left hp.frame_sub)

theorem argIn {i : Nat} (hi : i < Y.n) : InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [h.rd, h.wr]
  refine ⟨VG.Proof.MlKem.X86.Top.gR Y s₀, ?_, VG.Proof.MlKem.X86.arg_contains hi hp.sp'⟩
  rw [pushed_rd, P0_wr]
  rcases List.mem_append.mp hp.gwr with e | e
  · exact List.mem_append_left _ e
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ e)

omit hp in
theorem argEa {i : Nat} : (s.gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i := by
  rw [h.esp]; exact P0_argAddr s₀ i

end Ctx

end VG.Proof.MlKem.X86.Top

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.TopCall`. -/
section

/-!
# ML-KEM on x86 (32-bit): calls in the top-level functions

`call_piece` makes a call of verified code from a state satisfying `Ctx`, in a
frame of its arguments, as a `Piece`: the callee's precondition (`CallPre`),
its public data, and the regions it writes (within `W`) are what remains to
prove, and `Ctx` holds after it. The calls of the Keccak functions
(`absorb_call`, `pad_call`, `squeeze_call`) are made with their buffers named
as `Buf`s.

The callee sees the stack below `esp = E` as its arguments (`below E (4k)`),
its return address, and its own stack below that (`entry_regions`).
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (Repr bytesAt stateAt squeezeFrom absorb pad rates)

variable {Y : VG.Proof.MlKem.X86.Top.Lay} {lk : State → List Byte} {A B : State → State → Prop}

/-- A call of verified code, from `Ctx`. -/
theorem call_piece {k : Contract isa} {rs : List Reg} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c k) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    (hN : 4 * rs.length + stackUse c + 4 + 16 ≤ Y.stk) (rd wr : State → List Region)
    (hk : ∀ s₀ s, VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ CallPre k rs (rd s₀) (wr s₀) s)
    (hpub : ∀ s₀ s₀' s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → VG.Proof.MlKem.X86.Top.TPre Y s₀' → VG.Proof.MlKem.X86.Top.TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      rd s₀ = rd s₀' ∧ wr s₀ = wr s₀' ∧
      k.pub ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s').callEntry.withRegions (rd s₀) (wr s₀)))
    (hW : ∀ s₀, VG.Proof.MlKem.X86.Top.TPre Y s₀ → ∀ r ∈ wr s₀, ∃ r' ∈ VG.Proof.MlKem.X86.Top.W Y s₀, Region.Sub r r')
    (hQ : ∀ s₀ s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr s₀ ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ k.post ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀)) s₂) →
      B s₀ s') :
    Piece (VG.Proof.MlKem.X86.Top.TPre Y) (VG.Proof.MlKem.X86.Top.TPub Y lk) A B (callWith rs nm c) :=
  Piece.callWith hv.1 hv.2.1 hsp hne hrs rd wr
    (fun s₀ s hp ha => by rw [(hk s₀ s hp ha).1.esp, VG.Proof.MlKem.X86.Top.E1_nat s₀ hp.E0_big]; have := hp.sp; omega)
    (fun s₀ s hp ha => (hk s₀ s hp ha).2)
    (fun s₀ s₀' s s' hp hp' hq ha ha' => by
      obtain ⟨e₁, e₂, e₃⟩ := hpub s₀ s₀' s s' hp hp' hq ha ha'
      exact ⟨e₁, e₂, by rw [(hk _ _ hp ha).1.esp, (hk _ _ hp' ha').1.esp, hq.E1], e₃⟩)
    (fun s₀ s s' hp ha e₁ e₂ e₃ fr post => by
      have h := (hk s₀ s hp ha).1
      rw [h.esp] at fr
      refine hQ s₀ s s' hp ha (h.call e₁ e₂ e₃ fr fun r hr => ?_) e₃ fr post
      rcases List.mem_append.mp hr with hr | hr
      · exact hW s₀ hp r hr
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨VG.Proof.MlKem.X86.Top.cR Y s₀, TPre.cW, below_sub (by omega) (by rw [VG.Proof.MlKem.X86.Top.E1_nat s₀ hp.E0_big]; have := hp.sp; omega)⟩)

/-- `call_piece`, for `callRet`: the value the callee returns stays in `eax`. -/
theorem callR_piece {k : Contract isa} {rs : List Reg} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c k) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    (hN : 4 * rs.length + stackUse c + 4 + 16 ≤ Y.stk) (rd wr : State → List Region)
    (hk : ∀ s₀ s, VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ CallPre k rs (rd s₀) (wr s₀) s)
    (hpub : ∀ s₀ s₀' s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → VG.Proof.MlKem.X86.Top.TPre Y s₀' → VG.Proof.MlKem.X86.Top.TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      rd s₀ = rd s₀' ∧ wr s₀ = wr s₀' ∧
      k.pub ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s').callEntry.withRegions (rd s₀) (wr s₀)))
    (hW : ∀ s₀, VG.Proof.MlKem.X86.Top.TPre Y s₀ → ∀ r ∈ wr s₀, ∃ r' ∈ VG.Proof.MlKem.X86.Top.W Y s₀, Region.Sub r r')
    (hQ : ∀ s₀ s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr s₀ ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    Piece (VG.Proof.MlKem.X86.Top.TPre Y) (VG.Proof.MlKem.X86.Top.TPub Y lk) A B (callRet rs nm c) :=
  Piece.callRet hv.1 hv.2.1 hsp hne hrs rd wr
    (fun s₀ s hp ha => by rw [(hk s₀ s hp ha).1.esp, VG.Proof.MlKem.X86.Top.E1_nat s₀ hp.E0_big]; have := hp.sp; omega)
    (fun s₀ s hp ha => (hk s₀ s hp ha).2)
    (fun s₀ s₀' s s' hp hp' hq ha ha' => by
      obtain ⟨e₁, e₂, e₃⟩ := hpub s₀ s₀' s s' hp hp' hq ha ha'
      exact ⟨e₁, e₂, by rw [(hk _ _ hp ha).1.esp, (hk _ _ hp' ha').1.esp, hq.E1], e₃⟩)
    (fun s₀ s s' hp ha e₁ e₂ e₃ fr post => by
      have h := (hk s₀ s hp ha).1
      rw [h.esp] at fr
      refine hQ s₀ s s' hp ha (h.call e₁ e₂ e₃ fr fun r hr => ?_) e₃ fr post
      rcases List.mem_append.mp hr with hr | hr
      · exact hW s₀ hp r hr
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨VG.Proof.MlKem.X86.Top.cR Y s₀, TPre.cW, below_sub (by omega) (by rw [VG.Proof.MlKem.X86.Top.E1_nat s₀ hp.E0_big]; have := hp.sp; omega)⟩)

/-! ## The callee's view of the stack -/

theorem entry_regions {E : BitVec 32} {k K : Nat} (hE : 4 * k + 4 + K ≤ E.toNat) {R : Region}
    (hR : (below E (4 * k + 4 + K)).Disjoint R) :
    R.Disjoint (below E (4 * k)) ∧
      (⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64, 4⟩ : Region).Disjoint R ∧
      (⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint R := by
  have hr : Region.Sub ⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64, 4⟩ (below E (4 * k + 4 + K)) := by
    have := below_inner (sp := E) (a := 4) (b := 4 * k + 4 + K) (k := 4 * k) (by omega) hE
    have e : (⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64, 4⟩ : Region) = below (E - BitVec.ofNat 32 (4 * k)) 4 := by
      simp only [below]; congr 2; rw [BitVec.ofNat_add]; bv_omega
    rw [e]; exact this
  have hs : Region.Sub ⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64 - BitVec.ofNat 64 K, K⟩
      (below E (4 * k + 4 + K)) := by
    have := below_inner (sp := E) (a := K) (b := 4 * k + 4 + K) (k := 4 * k + 4) (by omega) hE
    have e : (⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region) =
        below (E - BitVec.ofNat 32 (4 * k + 4)) K := by
      simp only [below]
      rw [Taint.sub_setWidth (show K ≤ (E - BitVec.ofNat 32 (4 * k + 4)).toNat by rw [sub_toNat (by omega)]; omega)]
    rw [e]; exact this
  exact ⟨(hR.sub_left (below_sub (by omega) hE)).symm, hR.sub_left hr, hR.sub_left hs⟩

theorem entry_self {E : BitVec 32} {k K : Nat} (hE : 4 * k + 4 + K ≤ E.toNat) :
    (⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64, 4⟩ : Region).Disjoint (below E (4 * k)) ∧
      (⟨(E - BitVec.ofNat 32 (4 * k + 4)).setWidth 64 - BitVec.ofNat 64 K, K⟩ : Region).Disjoint
        (below E (4 * k)) := by
  constructor
  · intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    rw [Taint.sub_setWidth (by omega)] at h₁
    rw [Taint.sub_setWidth (by omega)] at h₂
    have := E.isLt
    have hE' : (E.setWidth 64).toNat = E.toNat := by
      simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
    generalize E.setWidth 64 = X at *
    bv_omega
  · intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    rw [Taint.sub_setWidth (by omega)] at h₁
    rw [Taint.sub_setWidth (by omega)] at h₂
    have := E.isLt
    have hE' : (E.setWidth 64).toNat = E.toNat := by
      simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
    generalize E.setWidth 64 = X at *
    bv_omega

/-- The callee's regions, within the caller's. -/
theorem covers_of {s : State} {n : Nat} {rd wr : List Region}
    (hrd : ∀ r ∈ rd, VG.Proof.MlKem.X86.Within r (s.rd ++ s.wr))
    (hwr : ∀ r ∈ wr, r = below (s.gpr .esp) (4 * n) ∨ VG.Proof.MlKem.X86.Within r s.wr) :
    Covers (rd ++ wr) (s.rd ++ below (s.gpr .esp) (4 * n) :: s.wr) ∧
      Covers wr (below (s.gpr .esp) (4 * n) :: s.wr) := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨r', h', o, hb, hl⟩ := hrd r hr
      refine ⟨r', ?_, o, hb, hl⟩
      rcases List.mem_append.mp h' with h' | h'
      · exact List.mem_append_left _ h'
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')
    · rcases hwr r hr with rfl | ⟨r', h', o, hb, hl⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), 0, by simp, by simp⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h'), o, hb, hl⟩
  · rcases hwr r hr with rfl | ⟨r', h', o, hb, hl⟩
    · exact ⟨_, List.mem_cons_self .., 0, by simp, by simp⟩
    · exact ⟨r', List.mem_cons_of_mem _ h', o, hb, hl⟩

theorem ctx_E {s₀ s : State} (hp : VG.Proof.MlKem.X86.Top.TPre Y s₀) (h : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s) {N : Nat} (hN : N + 16 ≤ Y.stk) :
    N ≤ (s.gpr .esp).toNat := by
  rw [h.esp, VG.Proof.MlKem.X86.Top.E1_nat s₀ hp.E0_big]; have := hp.sp; omega

theorem stk_sub {s₀ : State} (hp : VG.Proof.MlKem.X86.Top.TPre Y s₀) {a b : Nat} (hab : a ≤ b) (hN : b + 16 ≤ Y.stk) :
    Region.Sub (below (VG.Proof.MlKem.X86.Top.E1 s₀) a) (below (VG.Proof.MlKem.X86.Top.E1 s₀) b) :=
  below_sub hab (by rw [VG.Proof.MlKem.X86.Top.E1_nat s₀ hp.E0_big]; have := hp.sp; omega)

/-! ## The Keccak functions -/

/-- A call of `vg_keccak_absorb`, with the state at `(sa, so)`, the data `bD` and the working space at
`(wa, wo)`. -/
theorem absorb_call (sa so wa wo : Nat) (bD : Buf) (rate pos : Nat) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : (Y.okW ⟨sa, so, 200⟩ && Y.okW ⟨wa, wo, 640⟩ && Y.ok bD && Y.sep ⟨sa, so, 200⟩ ⟨wa, wo, 640⟩ &&
      Y.sep bD ⟨sa, so, 200⟩ && Y.sep bD ⟨wa, wo, 640⟩) = true) (hN : 56 ≤ Y.stk) (hlen : bD.len < 2 ^ 32)
    (hA : ∀ s₀ s, VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧
      VG.Proof.MlKem.X86.AbsArgs s (Buf.ptr s₀ ⟨sa, so, 200⟩) (bD.ptr s₀) (Buf.ptr s₀ ⟨wa, wo, 640⟩) rate pos bD.len)
    (hQ : ∀ s₀ s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨sa, so, 200⟩, ⟨wa, wo, 640⟩].map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨sa, so, 200⟩) rate msg → pos = msg.length % rate →
        Repr s'.mem (Buf.addr s₀ ⟨sa, so, 200⟩) rate (msg ++ bytesAt s.mem (bD.addr s₀) bD.len)) →
      B s₀ s') :
    Piece (VG.Proof.MlKem.X86.Top.TPre Y) (VG.Proof.MlKem.X86.Top.TPub Y lk) A B (callWith VG.Proof.MlKem.X86.rs6 "vg_keccak_absorb_scratch" Impl.Sha3.X86.Stream.absorb) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hS, hW⟩, hD⟩, dSW⟩, dDS⟩, dDW⟩ := hc
  have hS' := (Lay.okW_iff.mp hS).1
  have hW' := (Lay.okW_iff.mp hW).1
  refine VG.Proof.MlKem.X86.absorb_piece (fun s₀ => VG.Proof.MlKem.X86.Top.E1 s₀) (fun s₀ => Buf.ptr s₀ ⟨sa, so, 200⟩) (fun s₀ => bD.ptr s₀)
    (fun s₀ => Buf.ptr s₀ ⟨wa, wo, 640⟩) rate pos bD.len hr hpos hlen (fun s₀ s hp ha => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, hq.ptr hS', hq.ptr hD, hq.ptr hW'⟩)
    (fun s₀ s s' hp ha e₁ e₂ e₃ fr post => ?_)
  · obtain ⟨h, ha⟩ := hA s₀ s hp ha
    have hE : 40 ≤ (VG.Proof.MlKem.X86.Top.E1 s₀).toNat := by rw [VG.Proof.MlKem.X86.Top.E1_nat s₀ hp.E0_big]; have := hp.sp; omega
    exact ⟨h.esp, ha, ⟨hE, Buf.fit hp hS', Buf.fit hp hW', Buf.disj hp hS' hW' dSW,
      Buf.stkD hp hS' (by omega), Buf.stkD hp hW' (by omega)⟩, Buf.fit hp hD, Buf.disj hp hD hS' dDS,
      Buf.disj hp hD hW' dDW, Buf.stkD hp hD (by omega), Buf.within hp hD h.rd h.wr,
      Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr, Buf.withinW hp hW' (Lay.okW_iff.mp hW).2 h.wr⟩
  · have h := (hA s₀ s hp ha).1
    exact hQ s₀ s s' hp ha (h.call e₁ e₂ e₃ fr (Buf.frSub hp (bs := [⟨sa, so, 200⟩, ⟨wa, wo, 640⟩])
      (by simp [hS, hW]) (by omega))) e₃ fr post

/-- A call of `vg_keccak_pad`. -/
theorem pad_call (sa so wa wo : Nat) (rate pos sfx : Nat) (hr : rate ∈ rates) (hpos : pos < rate)
    (hc : (Y.okW ⟨sa, so, 200⟩ && Y.okW ⟨wa, wo, 640⟩ && Y.sep ⟨sa, so, 200⟩ ⟨wa, wo, 640⟩) = true)
    (hN : 56 ≤ Y.stk)
    (hA : ∀ s₀ s, VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧
      VG.Proof.MlKem.X86.PadArgs s (Buf.ptr s₀ ⟨sa, so, 200⟩) (Buf.ptr s₀ ⟨wa, wo, 640⟩) rate pos sfx)
    (hQ : ∀ s₀ s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨sa, so, 200⟩, ⟨wa, wo, 640⟩].map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 40]) s.mem s'.mem →
      (∀ msg, Repr s.mem (Buf.addr s₀ ⟨sa, so, 200⟩) rate msg → pos = msg.length % rate →
        stateAt s'.mem (Buf.addr s₀ ⟨sa, so, 200⟩) =
          absorb rate (pad rate ((BitVec.ofNat 32 sfx).setWidth 8) msg)) → B s₀ s') :
    Piece (VG.Proof.MlKem.X86.Top.TPre Y) (VG.Proof.MlKem.X86.Top.TPub Y lk) A B (callWith VG.Proof.MlKem.X86.rs5 "vg_keccak_pad_scratch" Impl.Sha3.X86.Stream.pad) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hS, hW⟩, dSW⟩ := hc
  have hS' := (Lay.okW_iff.mp hS).1
  have hW' := (Lay.okW_iff.mp hW).1
  refine VG.Proof.MlKem.X86.pad_piece (fun s₀ => VG.Proof.MlKem.X86.Top.E1 s₀) (fun s₀ => Buf.ptr s₀ ⟨sa, so, 200⟩) (fun s₀ => Buf.ptr s₀ ⟨wa, wo, 640⟩)
    rate pos sfx hr hpos (fun s₀ s hp ha => ?_) (fun s₀ s₀' _ _ hq => ⟨hq.E1, hq.ptr hS', hq.ptr hW'⟩)
    (fun s₀ s s' hp ha e₁ e₂ e₃ fr post => ?_)
  · obtain ⟨h, ha⟩ := hA s₀ s hp ha
    have hE : 40 ≤ (VG.Proof.MlKem.X86.Top.E1 s₀).toNat := by rw [VG.Proof.MlKem.X86.Top.E1_nat s₀ hp.E0_big]; have := hp.sp; omega
    exact ⟨h.esp, ha, ⟨hE, Buf.fit hp hS', Buf.fit hp hW', Buf.disj hp hS' hW' dSW,
      Buf.stkD hp hS' (by omega), Buf.stkD hp hW' (by omega)⟩,
      Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr, Buf.withinW hp hW' (Lay.okW_iff.mp hW).2 h.wr⟩
  · have h := (hA s₀ s hp ha).1
    exact hQ s₀ s s' hp ha (h.call e₁ e₂ e₃ fr (Buf.frSub hp (bs := [⟨sa, so, 200⟩, ⟨wa, wo, 640⟩])
      (by simp [hS, hW]) (by omega))) e₃ fr post

/-- A call of `vg_keccak_squeeze`, into `bO`. -/
theorem squeeze_call (sa so wa wo : Nat) (bO : Buf) (rate pos : Nat) (hr : rate ∈ rates) (hpos : pos ≤ rate)
    (hc : (Y.okW ⟨sa, so, 200⟩ && Y.okW ⟨wa, wo, 640⟩ && Y.okW bO && Y.sep ⟨sa, so, 200⟩ ⟨wa, wo, 640⟩ &&
      Y.sep ⟨sa, so, 200⟩ bO && Y.sep bO ⟨wa, wo, 640⟩) = true) (hN : 56 ≤ Y.stk) (hlen : bO.len < 2 ^ 32)
    (hA : ∀ s₀ s, VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧
      VG.Proof.MlKem.X86.AbsArgs s (Buf.ptr s₀ ⟨sa, so, 200⟩) (bO.ptr s₀) (Buf.ptr s₀ ⟨wa, wo, 640⟩) rate pos bO.len)
    (hQ : ∀ s₀ s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨sa, so, 200⟩, bO, ⟨wa, wo, 640⟩].map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 40]) s.mem s'.mem →
      bytesAt s'.mem (bO.addr s₀) bO.len =
        squeezeFrom rate (stateAt s.mem (Buf.addr s₀ ⟨sa, so, 200⟩)) pos bO.len →
      (∃ pos' ≤ rate, ∀ d, squeezeFrom rate (stateAt s'.mem (Buf.addr s₀ ⟨sa, so, 200⟩)) pos' d =
        squeezeFrom rate (stateAt s.mem (Buf.addr s₀ ⟨sa, so, 200⟩)) (pos + bO.len) d) → B s₀ s') :
    Piece (VG.Proof.MlKem.X86.Top.TPre Y) (VG.Proof.MlKem.X86.Top.TPub Y lk) A B (callWith VG.Proof.MlKem.X86.rs6 "vg_keccak_squeeze_scratch" Impl.Sha3.X86.Stream.squeeze) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hS, hW⟩, hO⟩, dSW⟩, dSO⟩, dOW⟩ := hc
  have hS' := (Lay.okW_iff.mp hS).1
  have hW' := (Lay.okW_iff.mp hW).1
  have hO' := (Lay.okW_iff.mp hO).1
  refine VG.Proof.MlKem.X86.squeeze_piece (fun s₀ => VG.Proof.MlKem.X86.Top.E1 s₀) (fun s₀ => Buf.ptr s₀ ⟨sa, so, 200⟩) (fun s₀ => bO.ptr s₀)
    (fun s₀ => Buf.ptr s₀ ⟨wa, wo, 640⟩) rate pos bO.len hr hpos hlen (fun s₀ s hp ha => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, hq.ptr hS', hq.ptr hO', hq.ptr hW'⟩)
    (fun s₀ s s' hp ha e₁ e₂ e₃ fr r₁ r₂ => ?_)
  · obtain ⟨h, ha⟩ := hA s₀ s hp ha
    have hE : 40 ≤ (VG.Proof.MlKem.X86.Top.E1 s₀).toNat := by rw [VG.Proof.MlKem.X86.Top.E1_nat s₀ hp.E0_big]; have := hp.sp; omega
    exact ⟨h.esp, ha, ⟨hE, Buf.fit hp hS', Buf.fit hp hW', Buf.disj hp hS' hW' dSW,
      Buf.stkD hp hS' (by omega), Buf.stkD hp hW' (by omega)⟩, Buf.fit hp hO', Buf.disj hp hS' hO' dSO,
      Buf.disj hp hO' hW' dOW, Buf.stkD hp hO' (by omega),
      Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr, Buf.withinW hp hO' (Lay.okW_iff.mp hO).2 h.wr,
      Buf.withinW hp hW' (Lay.okW_iff.mp hW).2 h.wr⟩
  · have h := (hA s₀ s hp ha).1
    exact hQ s₀ s s' hp ha (h.call e₁ e₂ e₃ fr (Buf.frSub hp (bs := [⟨sa, so, 200⟩, bO, ⟨wa, wo, 640⟩])
      (by simp [hS, hW, hO]) (by omega))) e₃ fr r₁ r₂

/-! ## Helpers for the primitives -/

/-- The regions a call writes: its buffers and its arguments' frame, within `W`. -/
theorem wr_sub {s₀ : State} (hp : VG.Proof.MlKem.X86.Top.TPre Y s₀) {bs : List Buf} (hbs : bs.all Y.okW = true) {a : Nat}
    (ha : a + 16 ≤ Y.stk) : ∀ r ∈ bs.map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) a], ∃ r' ∈ VG.Proof.MlKem.X86.Top.W Y s₀, Region.Sub r r' :=
  Buf.frSub hp hbs ha

/-- The frame a call leaves: its buffers, and the stack it uses. -/
theorem fr_conv {s₀ : State} (hp : VG.Proof.MlKem.X86.Top.TPre Y s₀) {bs : List Buf} {a N : Nat} (ha : a ≤ N) (hN : N + 16 ≤ Y.stk)
    {m m' : Mem} (fr : Frame (bs.map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) a] ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) N]) m m') :
    Frame (bs.map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) N]) m m' :=
  fr.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨below (VG.Proof.MlKem.X86.Top.E1 s₀) N, List.mem_append_right _ (List.mem_singleton_self _), VG.Proof.MlKem.X86.Top.stk_sub hp ha hN⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨below (VG.Proof.MlKem.X86.Top.E1 s₀) N, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩

/-- The bytes of a buffer, as the callee sees them. -/
theorem ent_keep {s₀ s : State} (hp : VG.Proof.MlKem.X86.Top.TPre Y s₀) (h : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s) {rs : List Reg} (hrs : Reg.esp ∉ rs)
    (fit : 4 * rs.length + 4 + 16 ≤ Y.stk) {b : Buf} (hb : Y.ok b = true) :
    ∀ i < b.len, (pushed rs s).callEntry.mem (b.addr s₀ + BitVec.ofNat 64 i) = s.mem (b.addr s₀ + BitVec.ofNat 64 i) :=
  fun _ hi => (callEntry_frame (VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 4 * rs.length + 4) (by omega)) hrs).bytes (R := b.rgn s₀)
    (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [h.esp]
      exact (Buf.stkD hp hb (N := 4 * rs.length + 4) (by omega)).symm)
    (by show b.len ≤ 2 ^ 64; have := Buf.fit hp hb; omega) hi

end VG.Proof.MlKem.X86.Top

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.TopPrim`. -/
section

/-!
# ML-KEM on x86 (32-bit): calls of the primitives in the top-level functions

Each primitive is called (`call_piece`) with its buffers named as `Buf`s, from
registers holding their addresses; its contract's precondition
(`Sig.contract`) at the callee's entry comes from `Ctx` and the buffers'
layout, and its postcondition is restated on the caller's memory.
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)

variable {Y : VG.Proof.MlKem.X86.Top.Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem ntt_nosp : NoSp Impl.MlKem.X86.ntt := NoSp.of_all (by decide +kernel)
theorem ntt_stack : stackUse Impl.MlKem.X86.ntt = 16 := by decide +kernel
theorem nttInv_nosp : NoSp Impl.MlKem.X86.nttInv := NoSp.of_all (by decide +kernel)
theorem nttInv_stack : stackUse Impl.MlKem.X86.nttInv = 16 := by decide +kernel

/-- `NTT` or `NTT⁻¹` in place, of the polynomial at `(fa, fo)`, with the scratch at `(sa, so)`. -/
theorem inPlace_call {t : VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (inPlaceContract X86.abi t 16)) (hsp : NoSp c) (hst : stackUse c = 16)
    (fa fo sa so : Nat)
    (hc : (Y.okW ⟨fa, fo, 1024⟩ && Y.okW ⟨sa, so, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨sa, so, 1024⟩) = true)
    (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨sa, so, 1024⟩ ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩, ⟨sa, so, 1024⟩].map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (t (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))) → B s₀ s') :
    Piece (VG.Proof.MlKem.X86.Top.TPre Y) (VG.Proof.MlKem.X86.Top.TPub Y lk) A B (callWith [.ecx, .eax] nm c) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hS⟩, dFS⟩ := hc
  have hF' := (Lay.okW_iff.mp hF).1
  have hS' := (Lay.okW_iff.mp hS).1
  refine VG.Proof.MlKem.X86.Top.call_piece hv hsp (by decide) (by decide) (by rw [hst]; simp only [List.length_cons, List.length_nil]; omega)
    (fun _ => []) (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩, Buf.rgn s₀ ⟨sa, so, 1024⟩, below (VG.Proof.MlKem.X86.Top.E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_) (fun s₀ hp r hr => ?_)
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx, hred⟩ := hA s₀ s hp ha
    have hE := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨sa, so, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (VG.Proof.MlKem.X86.Top.E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = VG.Proof.MlKem.X86.Top.E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have hE' : 28 ≤ (VG.Proof.MlKem.X86.Top.E1 s₀).toNat := by rw [← h.esp]; exact hE
    have bF := Buf.stkD hp hF' (N := 4 * 2 + 4 + 16) (by omega)
    have bS := Buf.stkD hp hS' (N := 4 * 2 + 4 + 16) (by omega)
    obtain ⟨rF₁, rF₂, rF₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' bF
    obtain ⟨rS₁, rS₂, rS₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' bS
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlKem.X86.Top.entry_self (E := VG.Proof.MlKem.X86.Top.E1 s₀) (k := 2) (K := 16) hE'
    have ef := callEntry_frame fit (by decide)
    have cv := VG.Proof.MlKem.X86.Top.covers_of (s := s) (n := 2) (rd := []) (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩,
        Buf.rgn s₀ ⟨sa, so, 1024⟩, below (VG.Proof.MlKem.X86.Top.E1 s₀) 8]) (fun r hr => absurd hr (by simp)) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr (Buf.withinW hp hF' (Lay.okW_iff.mp hF).2 h.wr)
      · exact .inr (Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (VG.Proof.MlKem.X86.Top.E1 s₀).isLt; omega,
      trivial, Buf.disj hp hF' hS' dFS, rF₁, rS₁, rF₂, rS₂, rA₂, rF₃, rS₃, rA₃,
      Buf.fit hp hF', Buf.fit hp hS', ?_⟩
    refine reduced_frame ef (fun r hr => ?_) hred
    rw [List.mem_singleton] at hr; subst hr; rw [h.esp]
    exact (bF.sub_left (below_sub (by simp) hE')).symm
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx', -⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr hS']
      · rw [hax, hax', hq.ptr hF']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨rfl, by simp only [Buf.rgn, hq.ptr hF', hq.ptr hS', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Buf.inW hp hF' (Lay.okW_iff.mp hF).2
    · exact Buf.inW hp hS' (Lay.okW_iff.mp hS).2
    · exact ⟨VG.Proof.MlKem.X86.Top.cR Y s₀, TPre.cW, VG.Proof.MlKem.X86.Top.stk_sub hp (by omega) (by have := hp.sp16; omega)⟩
  · obtain ⟨h, hax, -, -⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have hE' : 28 ≤ (VG.Proof.MlKem.X86.Top.E1 s₀).toNat := by rw [← h.esp]; exact VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega)
    have bF := Buf.stkD hp hF' (N := 4 * 2 + 4 + 16) (by omega)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, m₂] at post
    rw [polyAt_frame (callEntry_frame fit (by decide)) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [h.esp]
      exact (bF.sub_left (below_sub (by simp) hE')).symm)] at post
    refine hQ s₀ s s' hp ha h' e₃ (fr.sub fun r hr => ?_) post
    rw [hst] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨Buf.rgn s₀ ⟨fa, fo, 1024⟩, by simp, fun _ h => h⟩
    · exact ⟨Buf.rgn s₀ ⟨sa, so, 1024⟩, by simp, fun _ h => h⟩
    · exact ⟨below (VG.Proof.MlKem.X86.Top.E1 s₀) 28, by simp, VG.Proof.MlKem.X86.Top.stk_sub hp (by omega) (by omega)⟩
    · exact ⟨below (VG.Proof.MlKem.X86.Top.E1 s₀) 28, by simp, fun _ h => h⟩

theorem mul_nosp : NoSp Impl.MlKem.X86.multiplyNTTs := NoSp.of_all (by decide +kernel)
theorem mul_stack : stackUse Impl.MlKem.X86.multiplyNTTs = 16 := by decide +kernel

/-- `h ← MultiplyNTTs(f, g)`, with the polynomials at `(ha, ho)`, `(fa, fo)`, `(ga, go)` and the scratch
at `(sa, so)`, in `eax`, `ecx`, `edx` and `edi`. -/
theorem mul_call (oa oo fa fo ga go sa so : Nat)
    (hc : (Y.okW ⟨oa, oo, 1024⟩ && Y.ok ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.okW ⟨sa, so, 1024⟩ &&
      Y.sep ⟨oa, oo, 1024⟩ ⟨fa, fo, 1024⟩ && Y.sep ⟨oa, oo, 1024⟩ ⟨ga, go, 1024⟩ &&
      Y.sep ⟨oa, oo, 1024⟩ ⟨sa, so, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨sa, so, 1024⟩ &&
      Y.sep ⟨ga, go, 1024⟩ ⟨sa, so, 1024⟩) = true) (hN : 52 ≤ Y.stk)
    (hA : ∀ s₀ s, VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨oa, oo, 1024⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧ s.gpr .edx = Buf.ptr s₀ ⟨ga, go, 1024⟩ ∧
      s.gpr .edi = Buf.ptr s₀ ⟨sa, so, 1024⟩ ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨oa, oo, 1024⟩, ⟨sa, so, 1024⟩].map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        (multiplyNTTs (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) →
      B s₀ s') :
    Piece (VG.Proof.MlKem.X86.Top.TPre Y) (VG.Proof.MlKem.X86.Top.TPub Y lk) A B
      (callWith [.edi, .edx, .ecx, .eax] "vg_mlkem_multiply_ntts" Impl.MlKem.X86.multiplyNTTs) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hH, hF'⟩, hG'⟩, hS⟩, dHF⟩, dHG⟩, dHS⟩, dFS⟩, dGS⟩ := hc
  have hH' := (Lay.okW_iff.mp hH).1
  have hS' := (Lay.okW_iff.mp hS).1
  refine VG.Proof.MlKem.X86.Top.call_piece Mul.verified VG.Proof.MlKem.X86.Top.mul_nosp (by decide) (by decide)
    (by rw [VG.Proof.MlKem.X86.Top.mul_stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩, Buf.rgn s₀ ⟨ga, go, 1024⟩])
    (fun s₀ => [Buf.rgn s₀ ⟨oa, oo, 1024⟩, Buf.rgn s₀ ⟨sa, so, 1024⟩] ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 16])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => VG.Proof.MlKem.X86.Top.wr_sub hp (bs := [⟨oa, oo, 1024⟩, ⟨sa, so, 1024⟩]) (by simp [hH, hS]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx, hdx, hdi, rF, rG⟩ := hA s₀ s hp ha
    have hE' : 36 ≤ (VG.Proof.MlKem.X86.Top.E1 s₀).toNat := by rw [← h.esp]; exact VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 36) (by omega)
    have fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨oa, oo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have a2 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 2 = Buf.ptr s₀ ⟨ga, go, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
    have a3 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 3 = Buf.ptr s₀ ⟨sa, so, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hdi
    have eA : argAddr (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = (VG.Proof.MlKem.X86.Top.E1 s₀ - BitVec.ofNat 32 16).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.edi, .edx, .ecx, .eax] s).callEntry.gpr .esp = VG.Proof.MlKem.X86.Top.E1 s₀ - BitVec.ofNat 32 20 := by
      rw [callEntry_esp', h.esp]; rfl
    have bH := Buf.stkD hp hH' (N := 4 * 4 + 4 + 16) (by omega)
    have bF := Buf.stkD hp hF' (N := 4 * 4 + 4 + 16) (by omega)
    have bG := Buf.stkD hp hG' (N := 4 * 4 + 4 + 16) (by omega)
    have bS := Buf.stkD hp hS' (N := 4 * 4 + 4 + 16) (by omega)
    obtain ⟨rH₁, rH₂, rH₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' bH
    obtain ⟨rF₁, rF₂, rF₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' bF
    obtain ⟨rG₁, rG₂, rG₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' bG
    obtain ⟨rS₁, rS₂, rS₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' bS
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlKem.X86.Top.entry_self (E := VG.Proof.MlKem.X86.Top.E1 s₀) (k := 4) (K := 16) hE'
    have cv := VG.Proof.MlKem.X86.Top.covers_of (s := s) (n := 4) (rd := [Buf.rgn s₀ ⟨fa, fo, 1024⟩, Buf.rgn s₀ ⟨ga, go, 1024⟩])
      (wr := [Buf.rgn s₀ ⟨oa, oo, 1024⟩, Buf.rgn s₀ ⟨sa, so, 1024⟩] ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Buf.within hp hF' h.rd h.wr
        · exact Buf.within hp hG' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr (Buf.withinW hp hH' (Lay.okW_iff.mp hH).2 h.wr)
      · exact .inr (Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e
    sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
    have ek := @VG.Proof.MlKem.X86.Top.ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (VG.Proof.MlKem.X86.Top.E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp hH' hF' dHF, Buf.disj hp hH' hG' dHG, Buf.disj hp hH' hS' dHS, rH₁,
      Buf.disj hp hF' hS' dFS, rF₁, Buf.disj hp hG' hS' dGS, rG₁, rS₁, rH₂, rF₂, rG₂, rS₂, rA₂,
      rH₃, rF₃, rG₃, rS₃, rA₃, Buf.fit hp hH', Buf.fit hp hF', Buf.fit hp hG', Buf.fit hp hS',
      reduced_congr (ek hF') rF, reduced_congr (ek hG') rG⟩
  · obtain ⟨h, hax, hcx, hdx, hdi, -⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx', hdx', hdi', -⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.edi, Reg.edx, Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hdi, hdi', hq.ptr hS']
      · rw [hdx, hdx', hq.ptr hG']
      · rw [hcx, hcx', hq.ptr hF']
      · rw [hax, hax', hq.ptr hH']
    have fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 36) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨by simp only [Buf.rgn, hq.ptr hF', hq.ptr hG'], by simp only [Buf.rgn, hq.ptr hH', hq.ptr hS', hq.E1], ?_⟩
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.edi, .edx, .ecx, .eax] s').callEntry = e'
    sig_pub [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx, hdx, -⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 36) (by omega); simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨oa, oo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have a2 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 2 = Buf.ptr s₀ ⟨ga, go, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
    have ek := @VG.Proof.MlKem.X86.Top.ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e at post
    sig_post [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, m₂] at post
    rw [polyAt_congr (ek hF'), polyAt_congr (ek hG')] at post
    exact hQ s₀ s s' hp ha h' e₃ (VG.Proof.MlKem.X86.Top.fr_conv hp (a := 16) (N := 36) (by omega) (by omega)
      (by rw [VG.Proof.MlKem.X86.Top.mul_stack] at fr; exact fr)) post

end VG.Proof.MlKem.X86.Top

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.TopPrim2`. -/
section

/-!
# ML-KEM on x86 (32-bit): calls of the primitives of two arguments

As `TopPrim.lean`, for `vg_mlkem_add` and `vg_mlkem_sub` (`acc_call`),
`vg_mlkem_cbd2`, `vg_mlkem_encode12` and `vg_mlkem_decode12`, with their first
argument in `eax` and their second in `ecx`.
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)

variable {Y : VG.Proof.MlKem.X86.Top.Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem cbd2_nosp : NoSp Impl.MlKem.X86.cbd2 := NoSp.of_all (by decide +kernel)
theorem cbd2_stack : stackUse Impl.MlKem.X86.cbd2 = 16 := by decide +kernel
theorem encode12_nosp : NoSp Impl.MlKem.X86.encode12 := NoSp.of_all (by decide +kernel)
theorem encode12_stack : stackUse Impl.MlKem.X86.encode12 = 16 := by decide +kernel
theorem decode12_nosp : NoSp Impl.MlKem.X86.decode12 := NoSp.of_all (by decide +kernel)
theorem decode12_stack : stackUse Impl.MlKem.X86.decode12 = 16 := by decide +kernel
theorem add_nosp : NoSp Impl.MlKem.X86.add := NoSp.of_all (by decide +kernel)
theorem add_stack : stackUse Impl.MlKem.X86.add = 16 := by decide +kernel
theorem sub_nosp : NoSp Impl.MlKem.X86.sub := NoSp.of_all (by decide +kernel)
theorem sub_stack : stackUse Impl.MlKem.X86.sub = 16 := by decide +kernel

/-- `f ← op(f, g)` (`vg_mlkem_add` or `vg_mlkem_sub`), with `f` at `(fa, fo)` and `g` at `(ga, go)`. -/
theorem acc_call {op : VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly → VG.Spec.MlKem.Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (accSig.contract X86.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := 16)))
    (hsp : NoSp c) (hst : stackUse c = 16) (fa fo ga go : Nat)
    (hc : (Y.okW ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩) = true) (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨ga, go, 1024⟩ ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧ Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (op (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) → B s₀ s') :
    Piece (VG.Proof.MlKem.X86.Top.TPre Y) (VG.Proof.MlKem.X86.Top.TPub Y lk) A B (callWith [.ecx, .eax] nm c) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, d01⟩ := hc
  have h0' := (Lay.okW_iff.mp h0).1
  have h1' := h1
  refine VG.Proof.MlKem.X86.Top.call_piece hv hsp (by decide) (by decide)
    (by rw [hst]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨ga, go, 1024⟩]) (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => VG.Proof.MlKem.X86.Top.wr_sub hp (bs := [⟨fa, fo, 1024⟩]) (by simp [h0]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx, x0, x1⟩ := hA s₀ s hp ha
    have hE' : 28 ≤ (VG.Proof.MlKem.X86.Top.E1 s₀).toNat := by rw [← h.esp]; exact VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨ga, go, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (VG.Proof.MlKem.X86.Top.E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = VG.Proof.MlKem.X86.Top.E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have b0 := Buf.stkD hp h0' (N := 4 * 2 + 4 + 16) (by omega)
    have b1 := Buf.stkD hp h1' (N := 4 * 2 + 4 + 16) (by omega)
    obtain ⟨r0₁, r0₂, r0₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' b0
    obtain ⟨r1₁, r1₂, r1₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' b1
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlKem.X86.Top.entry_self (E := VG.Proof.MlKem.X86.Top.E1 s₀) (k := 2) (K := 16) hE'
    have cv := VG.Proof.MlKem.X86.Top.covers_of (s := s) (n := 2) (rd := [Buf.rgn s₀ ⟨ga, go, 1024⟩])
      (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp h1' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp h0' (Lay.okW_iff.mp h0).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    have ek := @VG.Proof.MlKem.X86.Top.ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (VG.Proof.MlKem.X86.Top.E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp h0' h1' d01, r0₁, r1₁, r0₂, r1₂, rA₂, r0₃, r1₃, rA₃,
      Buf.fit hp h0', Buf.fit hp h1', reduced_congr (ek h0') x0, reduced_congr (ek h1') x1⟩
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx', -⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr h1']
      · rw [hax, hax', hq.ptr h0']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨by simp only [Buf.rgn, hq.ptr h1'], by simp only [Buf.rgn, hq.ptr h0', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨ga, go, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have ek := @VG.Proof.MlKem.X86.Top.ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂] at post
    rw [polyAt_congr (ek h0'), polyAt_congr (ek h1')] at post
    exact hQ s₀ s s' hp ha h' e₃ (VG.Proof.MlKem.X86.Top.fr_conv hp (a := 8) (N := 28) (by omega) (by omega)
      (by rw [hst] at fr; exact fr)) post


/-- `f ← SamplePolyCBD₂(b)`, with the 128 bytes `b` at `(ba, bo)` and `f` at `(fa, fo)`. -/
theorem cbd2_call (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 128⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 128⟩ ⟨fa, fo, 1024⟩) = true) (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 128⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨fa, fo, 1024⟩)
    (hQ : ∀ s₀ s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (samplePolyCBD 2 (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 128⟩) 128)) → B s₀ s') :
    Piece (VG.Proof.MlKem.X86.Top.TPre Y) (VG.Proof.MlKem.X86.Top.TPub Y lk) A B (callWith [.ecx, .eax] "vg_mlkem_cbd2" Impl.MlKem.X86.cbd2) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, d01⟩ := hc
  have h0' := h0
  have h1' := (Lay.okW_iff.mp h1).1
  refine VG.Proof.MlKem.X86.Top.call_piece Cbd.verified VG.Proof.MlKem.X86.Top.cbd2_nosp (by decide) (by decide)
    (by rw [VG.Proof.MlKem.X86.Top.cbd2_stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨ba, bo, 128⟩]) (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => VG.Proof.MlKem.X86.Top.wr_sub hp (bs := [⟨fa, fo, 1024⟩]) (by simp [h1]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    have hE' : 28 ≤ (VG.Proof.MlKem.X86.Top.E1 s₀).toNat := by rw [← h.esp]; exact VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 128⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (VG.Proof.MlKem.X86.Top.E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = VG.Proof.MlKem.X86.Top.E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have b0 := Buf.stkD hp h0' (N := 4 * 2 + 4 + 16) (by omega)
    have b1 := Buf.stkD hp h1' (N := 4 * 2 + 4 + 16) (by omega)
    obtain ⟨r0₁, r0₂, r0₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' b0
    obtain ⟨r1₁, r1₂, r1₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' b1
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlKem.X86.Top.entry_self (E := VG.Proof.MlKem.X86.Top.E1 s₀) (k := 2) (K := 16) hE'
    have cv := VG.Proof.MlKem.X86.Top.covers_of (s := s) (n := 2) (rd := [Buf.rgn s₀ ⟨ba, bo, 128⟩])
      (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp h0' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp h1' (Lay.okW_iff.mp h1).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    have ek := @VG.Proof.MlKem.X86.Top.ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (VG.Proof.MlKem.X86.Top.E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp h0' h1' d01, r0₁, r1₁, r0₂, r1₂, rA₂, r0₃, r1₃, rA₃,
      Buf.fit hp h0', Buf.fit hp h1'⟩
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx'⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr h1']
      · rw [hax, hax', hq.ptr h0']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨by simp only [Buf.rgn, hq.ptr h0'], by simp only [Buf.rgn, hq.ptr h1', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 128⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have ek := @VG.Proof.MlKem.X86.Top.ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂] at post
    rw [bytesAt_congr (ek h0')] at post
    exact hQ s₀ s s' hp ha h' e₃ (VG.Proof.MlKem.X86.Top.fr_conv hp (a := 8) (N := 28) (by omega) (by omega)
      (by rw [VG.Proof.MlKem.X86.Top.cbd2_stack] at fr; exact fr)) post


/-- `out ← ByteEncode₁₂(f)`, with `f` at `(fa, fo)` and the 384 bytes `out` at `(oa, oo)`. -/
theorem encode12_call (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 384⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 384⟩) = true) (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨oa, oo, 384⟩ ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨oa, oo, 384⟩].map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 28]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 384⟩) 384 = encode12 (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (VG.Proof.MlKem.X86.Top.TPre Y) (VG.Proof.MlKem.X86.Top.TPub Y lk) A B (callWith [.ecx, .eax] "vg_mlkem_encode12" Impl.MlKem.X86.encode12) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, d01⟩ := hc
  have h0' := h0
  have h1' := (Lay.okW_iff.mp h1).1
  refine VG.Proof.MlKem.X86.Top.call_piece Encode12.verified VG.Proof.MlKem.X86.Top.encode12_nosp (by decide) (by decide)
    (by rw [VG.Proof.MlKem.X86.Top.encode12_stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩]) (fun s₀ => [Buf.rgn s₀ ⟨oa, oo, 384⟩] ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => VG.Proof.MlKem.X86.Top.wr_sub hp (bs := [⟨oa, oo, 384⟩]) (by simp [h1]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx, x0⟩ := hA s₀ s hp ha
    have hE' : 28 ≤ (VG.Proof.MlKem.X86.Top.E1 s₀).toNat := by rw [← h.esp]; exact VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨oa, oo, 384⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (VG.Proof.MlKem.X86.Top.E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = VG.Proof.MlKem.X86.Top.E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have b0 := Buf.stkD hp h0' (N := 4 * 2 + 4 + 16) (by omega)
    have b1 := Buf.stkD hp h1' (N := 4 * 2 + 4 + 16) (by omega)
    obtain ⟨r0₁, r0₂, r0₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' b0
    obtain ⟨r1₁, r1₂, r1₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' b1
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlKem.X86.Top.entry_self (E := VG.Proof.MlKem.X86.Top.E1 s₀) (k := 2) (K := 16) hE'
    have cv := VG.Proof.MlKem.X86.Top.covers_of (s := s) (n := 2) (rd := [Buf.rgn s₀ ⟨fa, fo, 1024⟩])
      (wr := [Buf.rgn s₀ ⟨oa, oo, 384⟩] ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp h0' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp h1' (Lay.okW_iff.mp h1).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    have ek := @VG.Proof.MlKem.X86.Top.ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (VG.Proof.MlKem.X86.Top.E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp h0' h1' d01, r0₁, r1₁, r0₂, r1₂, rA₂, r0₃, r1₃, rA₃,
      Buf.fit hp h0', Buf.fit hp h1', reduced_congr (ek h0') x0⟩
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx', -⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr h1']
      · rw [hax, hax', hq.ptr h0']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨by simp only [Buf.rgn, hq.ptr h0'], by simp only [Buf.rgn, hq.ptr h1', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨oa, oo, 384⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have ek := @VG.Proof.MlKem.X86.Top.ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂] at post
    rw [polyAt_congr (ek h0')] at post
    exact hQ s₀ s s' hp ha h' e₃ (VG.Proof.MlKem.X86.Top.fr_conv hp (a := 8) (N := 28) (by omega) (by omega)
      (by rw [VG.Proof.MlKem.X86.Top.encode12_stack] at fr; exact fr)) post


/-- `f ← ByteDecode₁₂(b)`, with the 384 bytes `b` at `(ba, bo)` and `f` at `(fa, fo)`. -/
theorem decode12_call (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 384⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 384⟩ ⟨fa, fo, 1024⟩) = true) (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 384⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨fa, fo, 1024⟩)
    (hQ : ∀ s₀ s s', VG.Proof.MlKem.X86.Top.TPre Y s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (decode12 (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 384⟩) 384)) → B s₀ s') :
    Piece (VG.Proof.MlKem.X86.Top.TPre Y) (VG.Proof.MlKem.X86.Top.TPub Y lk) A B (callWith [.ecx, .eax] "vg_mlkem_decode12" Impl.MlKem.X86.decode12) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, d01⟩ := hc
  have h0' := h0
  have h1' := (Lay.okW_iff.mp h1).1
  refine VG.Proof.MlKem.X86.Top.call_piece Decode12.verified VG.Proof.MlKem.X86.Top.decode12_nosp (by decide) (by decide)
    (by rw [VG.Proof.MlKem.X86.Top.decode12_stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨ba, bo, 384⟩]) (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => VG.Proof.MlKem.X86.Top.wr_sub hp (bs := [⟨fa, fo, 1024⟩]) (by simp [h1]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    have hE' : 28 ≤ (VG.Proof.MlKem.X86.Top.E1 s₀).toNat := by rw [← h.esp]; exact VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 384⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (VG.Proof.MlKem.X86.Top.E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = VG.Proof.MlKem.X86.Top.E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have b0 := Buf.stkD hp h0' (N := 4 * 2 + 4 + 16) (by omega)
    have b1 := Buf.stkD hp h1' (N := 4 * 2 + 4 + 16) (by omega)
    obtain ⟨r0₁, r0₂, r0₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' b0
    obtain ⟨r1₁, r1₂, r1₃⟩ := VG.Proof.MlKem.X86.Top.entry_regions hE' b1
    obtain ⟨rA₂, rA₃⟩ := VG.Proof.MlKem.X86.Top.entry_self (E := VG.Proof.MlKem.X86.Top.E1 s₀) (k := 2) (K := 16) hE'
    have cv := VG.Proof.MlKem.X86.Top.covers_of (s := s) (n := 2) (rd := [Buf.rgn s₀ ⟨ba, bo, 384⟩])
      (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (VG.Proof.MlKem.X86.Top.E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp h0' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp h1' (Lay.okW_iff.mp h1).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    have ek := @VG.Proof.MlKem.X86.Top.ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (VG.Proof.MlKem.X86.Top.E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp h0' h1' d01, r0₁, r1₁, r0₂, r1₂, rA₂, r0₃, r1₃, rA₃,
      Buf.fit hp h0', Buf.fit hp h1'⟩
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx'⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr h1']
      · rw [hax, hax', hq.ptr h0']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨by simp only [Buf.rgn, hq.ptr h0'], by simp only [Buf.rgn, hq.ptr h1', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := VG.Proof.MlKem.X86.Top.ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 384⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have ek := @VG.Proof.MlKem.X86.Top.ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂] at post
    rw [bytesAt_congr (ek h0')] at post
    exact hQ s₀ s s' hp ha h' e₃ (VG.Proof.MlKem.X86.Top.fr_conv hp (a := 8) (N := 28) (by omega) (by omega)
      (by rw [VG.Proof.MlKem.X86.Top.decode12_stack] at fr; exact fr)) post


end VG.Proof.MlKem.X86.Top

end
