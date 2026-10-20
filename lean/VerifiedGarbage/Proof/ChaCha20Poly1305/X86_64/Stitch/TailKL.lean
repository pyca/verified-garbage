module
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Chunk
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.StoreRow

import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Loop
import VerifiedGarbage.Proof.ChaCha20.X86_64.Xor
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ChaCha20 and Poly1305 together (x86-64): `tailKO`'s rounds

`Stitch.tailKO`'s eight blocks are `tailKMain`'s (`tailKMain_ok`) but for
their rounds, two loops (`roundsLK`, by `roundsL_ok`) that absorb only the
first `k` blocks at `rsi`: from `rsi` at the next four blocks, a double round
absorbing them (`sround4_ok`, `sround4V_ok`, from the state the round starts
at: `KL.round4`, `KLV.round4`), then double rounds absorbing none.
`tailKL_ok` is `tailKMain_ok` for them.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Proof.ChaCha20.X86_64.Avx2 (Holds HoldsV M8 M16 Consts Incs stR bufR slotsR dR5 plus
  setup_ok W2_frame incs_frame hiR_slots slotsR_sub slots_m8 loadV_ok storeV_ok)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.Poly1305.X86_64 (hval absorbRegs)
open VG.Spec.ChaCha20 (stateAt serialize innerBlock)
open VG.Spec.Poly1305 (P bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- After `n` of the kernel's double rounds from `s₁`, the first `j` blocks
at `q` absorbed: as `SR`, with `rsi` and `rdi` free. -/
structure KL (buf q : Addr) (R0 R1 : BitVec 64) (X : Nat) (V : Nat → CState) (s₁ : State)
    (n j : Nat) (s : State) : Prop where
  holds : Holds buf false (fun l => Nat.repeat innerBlock n (V l)) s
  m16 : ∀ l, s.lane .xmm15 l = rot16Mask
  frame : Frame [slotsR buf] s₁.mem s.mem
  gpr : ∀ r, r ∉ absorbRegs → r ≠ .rsi → r ≠ .rdi → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  acc : Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s

/-- As `KL`, with `vprold`: the states in their registers (`SIV`). -/
structure KLV (q : Addr) (R0 R1 : BitVec 64) (X : Nat) (V : Nat → CState) (s₁ : State)
    (n j : Nat) (s : State) : Prop where
  holds : HoldsV (fun l => Nat.repeat innerBlock n (V l)) s
  mem : s.mem = s₁.mem
  gpr : ∀ r, r ∉ absorbRegs → r ≠ .rsi → r ≠ .rdi → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  acc : Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s

theorem acc_keep {R0 R1 : BitVec 64} {X : Nat} {s s' : State} (h : Acc R0 R1 X s)
    (g : ∀ r, r ≠ .rsi → r ≠ .rdi → s'.gpr r = s.gpr r) : Acc R0 R1 X s' :=
  ⟨by rw [g _ (by decide) (by decide)]; exact h.r8, by rw [g _ (by decide) (by decide)]; exact h.r9,
    by rw [g _ (by decide) (by decide)]; exact h.r10, by rw [g _ (by decide) (by decide)]; exact h.h2,
    by simp only [hval, g Reg.r11 (by decide) (by decide), g Reg.rbx (by decide) (by decide),
      g Reg.rbp (by decide) (by decide)]; exact h.val⟩

/-- The blocks after `j` absorbed from a state `s`, whose memory has the
bytes of `s₁` there. -/
theorem acc_next {R0 R1 : BitVec 64} {X : Nat} {m₁ m : Mem} {q : Addr} {j d : Nat} {s : State}
    (hm : bytesAt m (q + BitVec.ofNat 64 (16 * j)) (16 * d) = bytesAt m₁ (q + BitVec.ofNat 64 (16 * j)) (16 * d))
    (h : Acc R0 R1 (absorbAll (rN R0 R1) (absorbAll (rN R0 R1) X (bytesAt m₁ q (16 * j)))
      (bytesAt m (q + BitVec.ofNat 64 (16 * j)) (16 * d))) s) :
    Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt m₁ q (16 * (j + d)))) s := by
  rw [hm, ← VG.Proof.Poly1305.absorbAll_append (by rw [VG.Proof.Poly1305.length_bytesAt]; omega),
    ← VG.Proof.Poly1305.bytesAt_add, ← Nat.mul_add] at h
  exact h

section
variable {buf q : Addr} {R0 R1 : BitVec 64} {X : Nat} {V : Nat → CState} {s₁ : State} {k : Nat}
  (hk : Key R0 R1) (hrcx : s₁.gpr .rcx = buf) (hb : bufR buf ∈ s₁.wr)
  (hk32 : 16 * k ≤ 512)
  (hd : (⟨q, 16 * k⟩ : Region).Disjoint (slotsR buf))
  (hin : ∀ off n, off + n ≤ 16 * k → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)

include hk hrcx hb hk32 hd hin in
/-- A double round absorbing the four blocks at `rsi`. -/
theorem KL.round4 (h8 : M8 s₁.mem buf) {n j : Nat} (hj : j + 4 ≤ k) {s : State}
    (h : KL buf q R0 R1 X V s₁ n j s) (hrsi : s.gpr .rsi = q + BitVec.ofNat 64 (16 * j)) :
    WP isa (sround4 0) s fun s' => KL buf q R0 R1 X V s₁ (n + 1) (j + 4) s' ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi := by
  have h8' : M8 s.mem buf := by
    have e : s.mem.readW (buf + BitVec.ofNat 64 160) 256 = s₁.mem.readW (buf + BitVec.ofNat 64 160) 256 :=
      h.frame.readW (Region.contains_self _ _) (by simpa using slots_m8 buf) (by decide)
    exact ⟨by rw [e]; exact h8.1, by rw [e]; exact h8.2⟩
  have hd' : (⟨q + BitVec.ofNat 64 (16 * j), 16 * 4⟩ : Region).Disjoint (slotsR buf) :=
    hd.sub_left (Offset.sub_base _ (by omega))
  have hin' : ∀ off n', off + n' ≤ 16 * 4 →
      InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    rw [h.rd, h.wr, Offset.add_add]
    exact hin _ _ (by omega)
  have i₀ : SI buf s false (fun l => Nat.repeat innerBlock n (V l))
      (AccTo (q + BitVec.ofNat 64 (16 * j)) R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s 0) s :=
    ⟨h.holds, h.m16, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, by
      simp only [AccTo, Nat.mul_zero]
      rw [show bytesAt s.mem (q + BitVec.ofNat 64 (16 * j)) 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact h.acc⟩
  refine WP.mono (sround4_ok hk (by rw [h.gpr _ (by decide) (by decide) (by decide), hrcx]) hrsi
    (by rw [h.wr]; exact hb) h8' hd' (by decide) hin' (j := 0) (by decide) i₀) fun s' h' => ?_
  have hm : bytesAt s.mem (q + BitVec.ofNat 64 (16 * j)) (16 * 4) =
      bytesAt s₁.mem (q + BitVec.ofNat 64 (16 * j)) (16 * 4) :=
    bytes_frame h.frame hd hk32 (by omega)
  refine ⟨⟨h'.holds, h'.m16, h.frame.trans h'.frame,
    fun r hr h₁ h₂ => by rw [h'.gpr r hr, h.gpr r hr h₁ h₂], by rw [h'.rd, h.rd], by rw [h'.wr, h.wr],
    acc_next hm h'.poly⟩, h'.gpr _ (by decide), h'.gpr _ (by decide)⟩

include hrcx hb in
/-- A double round absorbing nothing. -/
theorem KL.round0 (h8 : M8 s₁.mem buf) {n j : Nat} {s : State} (h : KL buf q R0 R1 X V s₁ n j s) :
    WP isa Impl.ChaCha20.X86_64.Avx2.doubleRound s fun s' => KL buf q R0 R1 X V s₁ (n + 1) j s' ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi := by
  have h8' : M8 s.mem buf := by
    have e : s.mem.readW (buf + BitVec.ofNat 64 160) 256 = s₁.mem.readW (buf + BitVec.ofNat 64 160) 256 :=
      h.frame.readW (Region.contains_self _ _) (by simpa using slots_m8 buf) (by decide)
    exact ⟨by rw [e]; exact h8.1, by rw [e]; exact h8.2⟩
  have i₀ : SI buf s false (fun l => Nat.repeat innerBlock n (V l))
      (AccTo q R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s 0) s :=
    ⟨h.holds, h.m16, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, by
      simp only [AccTo, Nat.mul_zero]
      rw [show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact h.acc⟩
  refine WP.mono (sround0_ok (by rw [h.gpr _ (by decide) (by decide) (by decide), hrcx]) (by rw [h.wr]; exact hb)
    h8' i₀) fun s' h' => ?_
  have a := h'.poly
  simp only [AccTo, Nat.mul_zero] at a
  rw [show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil] at a
  exact ⟨⟨h'.holds, h'.m16, h.frame.trans h'.frame,
    fun r hr h₁ h₂ => by rw [h'.gpr r hr, h.gpr r hr h₁ h₂], by rw [h'.rd, h.rd], by rw [h'.wr, h.wr], a⟩,
    h'.gpr _ (by decide), h'.gpr _ (by decide)⟩

include hk hin in
/-- `KL.round4` with `vprold`. -/
theorem KLV.round4 {n j : Nat} (hj : j + 4 ≤ k) {s : State}
    (h : KLV q R0 R1 X V s₁ n j s) (hrsi : s.gpr .rsi = q + BitVec.ofNat 64 (16 * j)) :
    WP isa (sround4V 0) s fun s' => KLV q R0 R1 X V s₁ (n + 1) (j + 4) s' ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi := by
  have hin' : ∀ off n', off + n' ≤ 16 * 4 →
      InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    rw [h.rd, h.wr, Offset.add_add]
    exact hin _ _ (by omega)
  have i₀ : SIV s (fun l => Nat.repeat innerBlock n (V l))
      (AccTo (q + BitVec.ofNat 64 (16 * j)) R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s 0) s :=
    ⟨h.holds, rfl, fun _ _ => rfl, rfl, rfl, by
      simp only [AccTo, Nat.mul_zero]
      rw [show bytesAt s.mem (q + BitVec.ofNat 64 (16 * j)) 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact h.acc⟩
  refine WP.mono (sround4V_ok hk hrsi hin' (j := 0) (by decide) i₀) fun s' h' => ?_
  have hm : bytesAt s.mem (q + BitVec.ofNat 64 (16 * j)) (16 * 4) =
      bytesAt s₁.mem (q + BitVec.ofNat 64 (16 * j)) (16 * 4) := by rw [h.mem]
  exact ⟨⟨h'.holds, by rw [h'.mem, h.mem], fun r hr h₁ h₂ => by rw [h'.gpr r hr, h.gpr r hr h₁ h₂],
    by rw [h'.rd, h.rd], by rw [h'.wr, h.wr], acc_next hm h'.poly⟩, h'.gpr _ (by decide), h'.gpr _ (by decide)⟩

/-- `KL.round0` with `vprold`. -/
theorem KLV.round0 {n j : Nat} {s : State} (h : KLV q R0 R1 X V s₁ n j s) :
    WP isa Impl.ChaCha20.X86_64.Avx2.doubleRoundV s fun s' => KLV q R0 R1 X V s₁ (n + 1) j s' ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi := by
  have i₀ : SIV s (fun l => Nat.repeat innerBlock n (V l))
      (AccTo q R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s 0) s :=
    ⟨h.holds, rfl, fun _ _ => rfl, rfl, rfl, by
      simp only [AccTo, Nat.mul_zero]
      rw [show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact h.acc⟩
  refine WP.mono (sround0V_ok i₀) fun s' h' => ?_
  have a := h'.poly
  simp only [AccTo, Nat.mul_zero] at a
  rw [show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil] at a
  exact ⟨⟨h'.holds, by rw [h'.mem, h.mem], fun r hr h₁ h₂ => by rw [h'.gpr r hr, h.gpr r hr h₁ h₂],
    by rw [h'.rd, h.rd], by rw [h'.wr, h.wr], a⟩, h'.gpr _ (by decide), h'.gpr _ (by decide)⟩

theorem KL.keep {n j : Nat} {s s' : State} (h : KL buf q R0 R1 X V s₁ n j s)
    (g : ∀ r, r ≠ .rsi → r ≠ .rdi → s'.gpr r = s.gpr r) (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : KL buf q R0 R1 X V s₁ n j s' := by
  refine ⟨fun k' hk' l q' hl hq' => ?_, fun l => by simpa only [State.lane, hx, hy] using h.m16 l,
    by rw [hm]; exact h.frame, fun r hr h₁ h₂ => by rw [g r h₁ h₂, h.gpr r hr h₁ h₂], by rw [hrd, h.rd],
    by rw [hwr, h.wr], acc_keep h.acc g⟩
  have e := h.holds k' hk' l q' hl hq'
  split
  · rename_i hreg
    simp only [hreg, ite_true] at e
    simpa only [Proof.ChaCha20.X86_64.Avx2.vw, State.lane, hx, hy] using e
  · rename_i hreg
    simp only [hreg] at e
    rw [hm]; exact e

theorem KLV.keep {n j : Nat} {s s' : State} (h : KLV q R0 R1 X V s₁ n j s)
    (g : ∀ r, r ≠ .rsi → r ≠ .rdi → s'.gpr r = s.gpr r) (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : KLV q R0 R1 X V s₁ n j s' :=
  ⟨fun k' hk' l q' hl hq' => by
      simpa only [Proof.ChaCha20.X86_64.Avx2.vw, State.lane, hx, hy] using h.holds k' hk' l q' hl hq',
    by rw [hm, h.mem], fun r hr h₁ h₂ => by rw [g r h₁ h₂, h.gpr r hr h₁ h₂], by rw [hrd, h.rd],
    by rw [hwr, h.wr], acc_keep h.acc g⟩

include hk hrcx hb hk32 hd hin in
/-- `roundsLK`: the kernel's ten double rounds, the first `k` blocks at `q`
absorbed, `rsi` back at `q` and `rdi` at `buf - 64`. -/
theorem roundsLK_ok (vl : Bool) (h1 : 1 ≤ k / 4) (h10 : k / 4 < 10) (hk4 : 4 * (k / 4) = k)
    (sk : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * k)) = BitVec.ofNat 64 (16 * k))
    (h8 : M8 s₁.mem buf) (h16 : M16 s₁.mem buf) (hrsi : s₁.gpr .rsi = q)
    (h : KL buf q R0 R1 X V s₁ 0 0 s₁) :
    WP isa (roundsLK vl k) s₁ fun s' => KL buf q R0 R1 X V s₁ 10 k s' ∧ s'.gpr .rsi = q ∧
      s'.gpr .rdi = buf - 64 := by
  have hc : ∀ {s : State}, KL buf q R0 R1 X V s₁ 10 k s → s.gpr .rcx = buf := fun h' => by
    rw [h'.gpr _ (by decide) (by decide) (by decide), hrcx]
  unfold roundsLK
  cases vl
  · refine WP.mono (roundsL_ok (KL buf q R0 R1 X V s₁) h1 h10 hk4 sk
      (fun _ _ _ _ h' g x y m rd wr => h'.keep g x y m rd wr)
      (fun n s hn h' hr => KL.round4 hk hrcx hb hk32 hd hin h8 (j := 4 * n) (show 4 * n + 4 ≤ k by omega) h' hr)
      (fun n s _ _ h' _ => KL.round0 hrcx hb h8 h') h hrsi) fun s' ⟨h', r', d'⟩ => ⟨h', r', by rw [d', hc h']⟩
  · simp only [ite_true]
    refine WP.seq (WP.mono (loadV_ok h.holds hrcx hb) fun s₂ ⟨h₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
    have i₂ : KLV q R0 R1 X V s₁ 0 0 s₂ :=
      ⟨h₂, m₂, fun r _ _ _ => by rw [g₂], rd₂, wr₂, acc_keep h.acc fun r _ _ => by rw [g₂]⟩
    refine WP.seq (WP.mono (roundsL_ok (KLV q R0 R1 X V s₁) h1 h10 hk4 sk
      (fun _ _ _ _ h' g x y m rd wr => h'.keep g x y m rd wr)
      (fun n s hn h' hr => KLV.round4 hk hin (j := 4 * n) (show 4 * n + 4 ≤ k by omega) h' hr)
      (fun n s _ _ h' _ => KLV.round0 h') i₂ (by rw [g₂, hrsi])) fun s₃ ⟨h₃, r₃, d₃⟩ => ?_)
    have c₃ : s₃.gpr .rcx = buf := by rw [h₃.gpr _ (by decide) (by decide) (by decide), hrcx]
    refine WP.mono (storeV_ok (s₀ := s₃) ⟨h₃.holds, rfl, rfl, rfl, rfl⟩ c₃ (by rw [h₃.wr]; exact hb)
      (by rw [h₃.mem]; exact h16)) fun s₄ h₄ => ?_
    refine ⟨⟨h₄.holds, h₄.m16, by rw [← h₃.mem]; exact h₄.frame,
      fun r hr h₁ h₂ => by rw [h₄.gpr, h₃.gpr r hr h₁ h₂], by rw [h₄.rd, h₃.rd], by rw [h₄.wr, h₃.wr],
      acc_keep h₃.acc fun r _ _ => by rw [h₄.gpr]⟩, by rw [h₄.gpr, r₃], by rw [h₄.gpr, d₃, c₃]⟩

end

/-- `tailKMain_ok` for `roundsLK`: the eight blocks of keystream from the
state at `st` (`buf - 64`) stored at `kA buf`, while the first `k` blocks at
`q` are absorbed. -/
theorem tailKL_ok (vl : Bool) {k : Nat} (h1 : 1 ≤ k / 4) (h10 : k / 4 < 10) (hk4 : 4 * (k / 4) = k)
    (hk32 : 16 * k ≤ 512)
    (sk : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * k)) = BitVec.ofNat 64 (16 * k))
    {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat} {st buf q : Addr} {s : State}
    (hrdi : s.gpr .rdi = st) (hrcx : s.gpr .rcx = buf) (hrsi : s.gpr .rsi = q) (hsb : buf - 64 = st)
    (hst : stR st ∈ s.wr) (hb : bufR buf ∈ s.wr) (hkr : kR buf ∈ s.wr)
    (hin : ∀ off n, off + n ≤ 16 * k → InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 off) n)
    (hc : Consts s.mem buf) (dsb : (stR st).Disjoint (bufR buf)) (dsk : (stR st).Disjoint (kR buf))
    (dbk : (bufR buf).Disjoint (kR buf)) (dqs : (⟨q, 16 * k⟩ : Region).Disjoint (slotsR buf))
    (hacc : Acc R0 R1 X s) :
    WP isa (.seq (.block Impl.ChaCha20.X86_64.Avx2.setup)
        (.seq (roundsLK vl k) (.block (Impl.ChaCha20.X86_64.Avx2.finishWith (storeRow kOff))))) s fun s' =>
        (∀ i < 512, s'.mem (kA buf + BitVec.ofNat 64 i) =
          (serialize (plus (fun j => Nat.repeat innerBlock 10 (ctr (stateAt s.mem st) j))
            (stateAt s.mem st) (i / 64))).getD (i % 64) 0) ∧
        Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s.mem q (16 * k))) s' ∧
        Frame [slotsR buf, kR buf] s.mem s'.mem ∧
        (∀ r, r ∉ absorbRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (WP.mono (setup_ok hrdi hrcx hst hb hc)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_)
  have c₁ : Consts s₁.mem buf := by rw [m₁]; exact hc.w2 (by decide) y₁ y₂
  have F₁ : Frame [slotsR buf] s.mem s₁.mem := by
    rw [m₁]; exact W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  have q₁ : bytesAt s₁.mem q (16 * k) = bytesAt s.mem q (16 * k) := by
    have := bytes_frame F₁ dqs hk32 (j := 0) (n := 16 * k) (by omega)
    simpa using this
  have h0 : KL buf q R0 R1 X (fun j => ctr (stateAt s.mem st) j) s₁ 0 0 s₁ :=
    ⟨hh, h15, Frame.refl _ _, fun _ _ _ _ => rfl, rfl, rfl, by
      rw [show 16 * 0 = 0 from rfl, show bytesAt s₁.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact ⟨by rw [g₁]; exact hacc.r8, by rw [g₁]; exact hacc.r9, by rw [g₁]; exact hacc.r10,
        by rw [g₁]; exact hacc.h2, by simp only [hval, g₁]; exact hacc.val⟩⟩
  refine WP.seq (WP.mono (roundsLK_ok hk (by rw [g₁, hrcx]) (by rw [wr₁]; exact hb) hk32 dqs
    (by rw [rd₁, wr₁]; exact hin) vl h1 h10 hk4 sk c₁.m8 ⟨c₁.lo16, c₁.hi16⟩ (by rw [g₁, hrsi]) h0)
    fun s₂ ⟨h₂, r₂, d₂⟩ => ?_)
  have F₂ : Frame [slotsR buf] s.mem s₂.mem := F₁.trans h₂.frame
  have gk : ∀ r, r ∉ absorbRegs → s₂.gpr r = s.gpr r := fun r hr => by
    by_cases e₁ : r = .rsi
    · subst e₁; rw [r₂, hrsi]
    by_cases e₂ : r = .rdi
    · subst e₂; rw [d₂, hsb, hrdi]
    rw [h₂.gpr r hr e₁ e₂, g₁]
  have wr₂ : s₂.wr = s.wr := by rw [h₂.wr, wr₁]
  have inc₂ : Incs buf s₂.mem := incs_frame hc.inc F₂ (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hiR_slots _)
  refine WP.mono (finishK_ok h₂.holds (st := st) (by rw [gk _ (by decide), hrdi]) (by rw [gk _ (by decide), hrcx])
    (by rw [wr₂]; exact hst) (by rw [wr₂]; exact hb) (by rw [wr₂]; exact hkr) inc₂ dsb dsk dbk)
    fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  have hS : stateAt s₂.mem st = stateAt s.mem st :=
    Proof.ChaCha20.X86_64.Xor.stateAt_frame F₂ (by simpa using dsb.sub_right (slotsR_sub buf))
  refine ⟨fun i hi => by rw [d₃ i hi, hS], ?_, (F₂.mono (by simp)).trans f₃,
    fun r hr => by rw [g₃, gk r hr], by rw [rd₃, h₂.rd, rd₁], by rw [wr₃, wr₂]⟩
  have a₂ := h₂.acc
  rw [q₁] at a₂
  exact ⟨by rw [g₃]; exact a₂.r8, by rw [g₃]; exact a₂.r9, by rw [g₃]; exact a₂.r10, by rw [g₃]; exact a₂.h2,
    by simp only [hval, g₃]; exact a₂.val⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
