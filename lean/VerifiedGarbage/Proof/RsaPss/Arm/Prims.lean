module

public import VerifiedGarbage.Proof.RsaPss.Arm.Step
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytes
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytes
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytes
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PSS on ARMv7: the byte loops of `Impl/Bignum/Arm/`

`maskBytes` with a zero mask (`zero_vp`), `copyBytes` (`copy_vp`) and
`compareBytes` (`cmp_vp`), from a state of the body (`Ctx`) with their
registers set to public pointers and lengths, keeping any fact about memory
(`Inv`) that their writes do not reach.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (Rest)

/-- Byte `i` of the buffer at `p`. -/
abbrev byteAt (p : BitVec 32) (i : Nat) : Addr := State.addr p + BitVec.ofNat 64 i

/-- `n` bytes at `p` that the body may write: in the frame or a writable
buffer, apart from the slot of `scratch`, not wrapping around. -/
structure WBuf (L : Lay) (p : BitVec 32) (n : Nat) : Prop where
  fit : p.toNat + n ≤ 2 ^ 32
  n32 : n < 2 ^ 32
  w : ∃ R ∈ L.FR :: L.rw, R.Contains (State.addr p) n
  slot : (slotR L sS).Disjoint ⟨State.addr p, n⟩

/-- `n` bytes at `p` that the body may read. -/
structure RBuf (L : Lay) (p : BitVec 32) (n : Nat) : Prop where
  fit : p.toNat + n ≤ 2 ^ 32
  n32 : n < 2 ^ 32
  r : ∃ R ∈ L.ro ++ L.FR :: L.rw, R.Contains (State.addr p) n

variable {L : Lay} {scr : BitVec 32}

theorem byte32 {p : BitVec 32} {n i : Nat} (h : p.toNat + n ≤ 2 ^ 32) (hi : i < n) :
    State.addr (p + BitVec.ofNat 32 i) = byteAt p i := addr_add (by omega)

theorem contains_byte {R : Region} {p : BitVec 32} {n i : Nat} (hc : R.Contains (State.addr p) n)
    (fit : p.toNat + n ≤ 2 ^ 32) (hi : i < n) : R.Contains (byteAt p i) 1 :=
  hc.byte (by rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi)

theorem WBuf.inW {p : BitVec 32} {n : Nat} (hb : WBuf L p n) {σ s : State} (hs : L.St σ s) {i : Nat}
    (hi : i < n) : InRegions s.wr (byteAt p i) 1 := by
  obtain ⟨R, hR, hc⟩ := hb.w
  refine ⟨R, ?_, contains_byte hc hb.fit hi⟩
  rw [hs.wr, hs.ok.wr]
  rcases List.mem_cons.mp hR with rfl | hR
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR)

theorem RBuf.inR {p : BitVec 32} {n : Nat} (hb : RBuf L p n) {σ s : State} (hs : L.St σ s) {i : Nat}
    (hi : i < n) : InRegions (s.rd ++ s.wr) (byteAt p i) 1 := by
  obtain ⟨R, hR, hc⟩ := hb.r
  refine ⟨R, ?_, contains_byte hc hb.fit hi⟩
  rw [hs.rd, hs.wr, hs.ok.rd, hs.ok.wr]
  rcases List.mem_append.mp hR with hR | hR
  · exact List.mem_append_left _ (List.mem_append_left _ hR)
  · rcases List.mem_cons.mp hR with rfl | hR
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR))

theorem WBuf.rbuf {p : BitVec 32} {n : Nat} (hb : WBuf L p n) : RBuf L p n :=
  ⟨hb.fit, hb.n32, let ⟨R, hR, hc⟩ := hb.w; ⟨R, List.mem_append_right _ hR, hc⟩⟩

/-- The bytes of the buffer are distinct addresses. -/
theorem byteAt_inj {p : BitVec 32} {n i j : Nat} (h : p.toNat + n ≤ 2 ^ 32) (hi : i < n) (hj : j < n)
    (e : byteAt p i = byteAt p j) : i = j :=
  Classical.byContradiction fun hne => Offset.add_ofNat_ne (State.addr p) (a := i) (b := j) (by omega) (by omega) hne e

/-- An address of the buffer's region is one of its bytes. -/
theorem mem_region {p : BitVec 32} {n : Nat} {a : Addr} (hc : (⟨State.addr p, n⟩ : Region).Contains a 1) : ∃ j < n, a = byteAt p j := by
  refine ⟨(a - State.addr p).toNat, by simp only [Region.Contains] at hc; omega, ?_⟩
  show a = State.addr p + BitVec.ofNat 64 (a - State.addr p).toNat
  rw [show BitVec.ofNat 64 (a - State.addr p).toNat = a - State.addr p from BitVec.eq_of_toNat_eq (by simp),
    BitVec.add_comm, BitVec.sub_add_cancel]

theorem frame_of_outside {p : BitVec 32} {n : Nat} {m m' : Mem} (h : p.toNat + n ≤ 2 ^ 32)
    (hm : ∀ a, (∀ j < n, a ≠ State.addr (p + BitVec.ofNat 32 j)) → m' a = m a) :
    Frame [⟨State.addr p, n⟩] m m' := by
  intro a ha
  refine hm a fun j hj e => ha _ (List.mem_singleton_self _) ?_
  rw [e, byte32 h hj]
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

/-- `maskBytes` with a zero mask: zeros at `p`. -/
theorem zero_vp {p : BitVec 32} {n : Nat} (hb : WBuf L p n) (hn : 0 < n)
    {Inv : State → Mem → Prop} (hI : ∀ σ m m', Inv σ m → Frame [⟨State.addr p, n⟩] m m' → Inv σ m') :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .r0 = p ∧ s.gpr .r2 = 0 ∧ s.gpr .lr = BitVec.ofNat 32 n)
      Impl.Bignum.Arm.maskBytes
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ ∀ i < n, s.mem (byteAt p i) = 0) := by
  have fit := hb.fit
  refine VP.ct VG.Proof.Bignum.Arm.maskBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1],
    by rw [h₁.2.2.2.2, h₂.2.2.2.2]⟩) fun σ s ⟨hc, hi, r0, r2, lr⟩ => ?_
  have ctx : VG.Proof.Bignum.Arm.MaskCtx s p n :=
    ⟨hb.n32, fun i hi => by rw [byte32 fit hi]; exact (hb.rbuf).inR hc.st hi,
      fun i hi => by rw [byte32 fit hi]; exact hb.inW hc.st hi,
      fun i hi j hj e => byteAt_inj fit hi hj (by rwa [byte32 fit hi, byte32 fit hj] at e)⟩
  refine WP.mono (VG.Proof.Bignum.Arm.maskBytes_ok s ctx hn r0 lr) fun t inv => ?_
  have fr : Frame [⟨State.addr p, n⟩] s.mem t.mem := frame_of_outside fit inv.outside
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) inv.rest.rd inv.rest.wr inv.rest.sp, hI σ _ _ hi fr,
    fun i hi' => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨R, hR, hc'⟩ := hb.w
    refine ⟨R, ?_, fun a ha => hc'.byte ?_⟩
    · rcases List.mem_cons.mp hR with rfl | hR
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hR)
    · simp only [Region.Contains] at ha; omega
  · simp only [List.mem_singleton] at hr; subst hr; exact hb.slot
  · rw [← byte32 fit hi', inv.masked i hi', r2]
    exact BitVec.and_zero

/-- `copyBytes`: the `n` bytes at `src`, whatever they are in the run from
`σ` (`f σ`), copied to `dst`. -/
theorem copy_vp {src dst : BitVec 32} {n : Nat} (hd : WBuf L dst n) (hs : RBuf L src n)
    (hsep : Region.Disjoint ⟨State.addr src, n⟩ ⟨State.addr dst, n⟩) (hn : 0 < n)
    {Inv : State → Mem → Prop} (hI : ∀ σ m m', Inv σ m → Frame [⟨State.addr dst, n⟩] m m' → Inv σ m')
    {f : State → Nat → Byte} :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .r0 = dst ∧ s.gpr .r1 = src ∧
        s.gpr .lr = BitVec.ofNat 32 n ∧ ∀ i < n, s.mem (byteAt src i) = f σ i)
      Impl.Bignum.Arm.copyBytes
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ ∀ i < n, s.mem (byteAt dst i) = f σ i) := by
  have fit := hd.fit
  have fis := hs.fit
  refine VP.ct VG.Proof.Bignum.Arm.copyBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1],
    by rw [h₁.2.2.2.1, h₂.2.2.2.1], by rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]⟩)
    fun σ s ⟨hc, hi, r0, r1, lr, hf⟩ => ?_
  have ctx : VG.Proof.Bignum.Arm.CopyCtx s src dst n :=
    ⟨hd.n32, fun i hi => by rw [byte32 fis hi]; exact hs.inR hc.st hi,
      fun i hi => by rw [byte32 fit hi]; exact hd.inW hc.st hi,
      fun i hi j hj e => by
        rw [byte32 fis hi, byte32 fit hj] at e
        exact hsep _ (contains_byte (Region.contains_self _ _) fis hi)
          (e ▸ contains_byte (Region.contains_self _ _) fit hj),
      fun i hi j hj e => byteAt_inj fit hi hj (by rwa [byte32 fit hi, byte32 fit hj] at e)⟩
  refine WP.mono (VG.Proof.Bignum.Arm.copyBytes_ok s ctx hn r1 r0 lr) fun t inv => ?_
  have fr : Frame [⟨State.addr dst, n⟩] s.mem t.mem := frame_of_outside fit inv.outside
  refine ⟨hc.write fr (fun r hr => ?_) (fun r hr => ?_) inv.rest.rd inv.rest.wr inv.rest.sp, hI σ _ _ hi fr,
    fun i hi' => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨R, hR, hc'⟩ := hd.w
    refine ⟨R, ?_, fun a ha => hc'.byte ?_⟩
    · rcases List.mem_cons.mp hR with rfl | hR
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hR)
    · simp only [Region.Contains] at ha; omega
  · simp only [List.mem_singleton] at hr; subst hr; exact hd.slot
  · rw [← byte32 fit hi', inv.copied i hi', byte32 fis hi', hf i hi']

/-- `compareBytes`: `r2` is zero exactly when the `n` bytes at `a` and at `b`
are equal. -/
theorem cmp_vp {a b : BitVec 32} {n : Nat} (ha : RBuf L a n) (hb : RBuf L b n) (hn : 0 < n)
    {Inv : State → Mem → Prop} {f g : State → Nat → Byte} :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .r0 = a ∧ s.gpr .r1 = b ∧
        s.gpr .lr = BitVec.ofNat 32 n ∧ s.gpr .r2 = 0 ∧ (∀ i < n, s.mem (byteAt a i) = f σ i) ∧
        ∀ i < n, s.mem (byteAt b i) = g σ i)
      Impl.Bignum.Arm.compareBytes
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ (s.gpr .r2 = 0 ↔ ∀ i < n, f σ i = g σ i)) := by
  have fa := ha.fit
  have fb := hb.fit
  refine VP.ct VG.Proof.Bignum.Arm.compareBytes_ct (fun _ _ _ _ h₁ h₂ => ⟨by rw [h₁.2.2.1, h₂.2.2.1],
    by rw [h₁.2.2.2.1, h₂.2.2.2.1], by rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]⟩)
    fun σ s ⟨hc, hi, r0, r1, lr, r2, hf, hg⟩ => ?_
  have ctx : VG.Proof.Bignum.Arm.CompareCtx s a b n :=
    ⟨ha.n32, fun i hi => by rw [byte32 fa hi]; exact ha.inR hc.st hi,
      fun i hi => by rw [byte32 fb hi]; exact hb.inR hc.st hi⟩
  refine WP.mono (VG.Proof.Bignum.Arm.compareBytes_ok s ctx hn r0 r1 lr r2) fun t inv => ?_
  refine ⟨hc.regs inv.rest.rd inv.rest.wr inv.rest.sp inv.mem, by rw [inv.mem]; exact hi, ?_⟩
  rw [inv.equal]
  refine forall_congr' fun i => imp_congr_right fun hi' => ?_
  rw [byte32 fa hi', byte32 fb hi', hf i hi', hg i hi']

end VG.Proof.RsaPss.Arm
