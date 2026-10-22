module

public import VerifiedGarbage.Proof.RsaPss.X86.Base
public import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Loops
import VerifiedGarbage.Proof.Bignum.X86.CopyBytes
import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt

/-!
# RSASSA-PSS on x86: the byte loops of `Impl/Bignum/X86/`

`zeroLoop` (`zero_vp`) and `copyBytes` (`copy_vp`), from a state of the body
(`Ctx`) with their registers set to public pointers and lengths, keeping any
fact about memory (`Inv`) that their writes do not reach.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

/-- Byte `i` of the buffer at `p`. -/
abbrev byteAt (p : BitVec 32) (i : Nat) : Addr := p.setWidth 64 + BitVec.ofNat 64 i

/-- `n` bytes at `p` that the body may write: in the frame or a writable
buffer, not wrapping around. -/
structure WBuf (L : Lay) (p : BitVec 32) (n : Nat) : Prop where
  fit : p.toNat + n ≤ 2 ^ 32
  n32 : n < 2 ^ 32
  w : ∃ R ∈ L.FR :: L.rw, R.Contains (p.setWidth 64) n

/-- `n` bytes at `p` that the body may read. -/
structure RBuf (L : Lay) (p : BitVec 32) (n : Nat) : Prop where
  fit : p.toNat + n ≤ 2 ^ 32
  n32 : n < 2 ^ 32
  r : ∃ R ∈ L.ro ++ L.FR :: L.rw, R.Contains (p.setWidth 64) n

variable {L : Lay} {scr : BitVec 32}

theorem byte32 {p : BitVec 32} {n i : Nat} (h : p.toNat + n ≤ 2 ^ 32) (hi : i < n) :
    (p + BitVec.ofNat 32 i).setWidth 64 = byteAt p i := addr_eq (by omega)

theorem contains_byte {R : Region} {p : BitVec 32} {n i : Nat} (hc : R.Contains (p.setWidth 64) n)
    (fit : p.toNat + n ≤ 2 ^ 32) (hi : i < n) : R.Contains (byteAt p i) 1 :=
  hc.byte (by rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi)

theorem WBuf.inW {p : BitVec 32} {n : Nat} (hb : WBuf L p n) {σ s : State} (hs : L.St σ s) {i : Nat}
    (hi : i < n) : InRegions s.wr (byteAt p i) 1 := by
  obtain ⟨R, hR, hc⟩ := hb.w
  refine ⟨R, ?_, contains_byte hc hb.fit hi⟩
  rw [hs.wr, hs.ok.wr]
  rcases List.mem_cons.mp hR with rfl | hR
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hR))

theorem RBuf.inR {p : BitVec 32} {n : Nat} (hb : RBuf L p n) {σ s : State} (hs : L.St σ s) {i : Nat}
    (hi : i < n) : InRegions (s.rd ++ s.wr) (byteAt p i) 1 := by
  obtain ⟨R, hR, hc⟩ := hb.r
  refine ⟨R, ?_, contains_byte hc hb.fit hi⟩
  rw [hs.rd, hs.wr, hs.ok.rd, hs.ok.wr]
  rcases List.mem_append.mp hR with hR | hR
  · exact List.mem_append_left _ hR
  · rcases List.mem_cons.mp hR with rfl | hR
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hR)))

theorem WBuf.rbuf {p : BitVec 32} {n : Nat} (hb : WBuf L p n) : RBuf L p n :=
  ⟨hb.fit, hb.n32, let ⟨R, hR, hc⟩ := hb.w; ⟨R, List.mem_append_right _ hR, hc⟩⟩

/-- A range written within a buffer the body may write. -/
theorem WBuf.sub {p : BitVec 32} {n : Nat} (hb : WBuf L p n) : ∃ R ∈ L.W, Region.Sub ⟨p.setWidth 64, n⟩ R := by
  obtain ⟨R, hR, hc⟩ := hb.w
  refine ⟨R, ?_, fun a ha => hc.byte ?_⟩
  · rcases List.mem_cons.mp hR with rfl | hR
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hR)
  · simp only [Region.Contains] at ha; omega

/-- The bytes of the buffer are distinct addresses. -/
theorem byteAt_inj {p : BitVec 32} {n i j : Nat} (h : p.toNat + n ≤ 2 ^ 32) (hi : i < n) (hj : j < n)
    (e : byteAt p i = byteAt p j) : i = j :=
  Classical.byContradiction fun hne => Offset.add_ofNat_ne (p.setWidth 64) (a := i) (b := j) (by omega) (by omega) hne e

theorem frame_of_outside {p : BitVec 32} {n : Nat} {m m' : Mem} (h : p.toNat + n ≤ 2 ^ 32)
    (hm : ∀ a, (∀ j < n, a ≠ (p + BitVec.ofNat 32 j).setWidth 64) → m' a = m a) :
    Frame [⟨p.setWidth 64, n⟩] m m' := by
  intro a ha
  refine hm a fun j hj e => ha _ (List.mem_singleton_self _) ?_
  rw [e, byte32 h hj]
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

/-- `zeroLoop`: zeros at `p`. -/
theorem zero_vp {p : BitVec 32} {n : Nat} (hb : WBuf L p n) (hn : 0 < n)
    {Inv : State → Mem → Prop} (hI : ∀ σ m m', Inv σ m → Frame [⟨p.setWidth 64, n⟩] m m' → Inv σ m') :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .esi = p ∧ s.gpr .ecx = BitVec.ofNat 32 n ∧ s.gpr .eax = 0)
      zeroLoop
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ ∀ i < n, s.mem (byteAt p i) = 0) := by
  have fit := hb.fit
  refine VP.taint [.esi, .ecx] zeroLoop_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hc, hi, si, cx, ax⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  have hw : InRegions s.wr (p.setWidth 64) n := by
    obtain ⟨R, hR, hc'⟩ := hb.w
    refine ⟨R, ?_, hc'⟩
    rw [hc.st.wr, hc.st.ok.wr]
    rcases List.mem_cons.mp hR with rfl | hR
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hR))
  refine WP.mono (zero_ok hn hb.n32 fit si cx ax hw) fun t ht => ?_
  have fr : Frame [⟨p.setWidth 64, n⟩] s.mem t.mem := by
    rw [ht.mem]
    have := Proof.RsaPkcs1Sig.frame_writeBytes s.mem (p.setWidth 64) (List.replicate n 0)
    simpa using this
  refine ⟨hc.write fr (fun r hr => ?_) ht.rd ht.wr (ht.other _ (by decide) (by decide))
    (ht.other _ (by decide) (by decide)), hI σ _ _ hi fr, fun i hi' => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hb.sub
  · rw [ht.mem]
    have := congrArg (fun l => l.getD i 0) (Proof.RsaPkcs1Sig.bytesAt_writeBytes s.mem (p.setWidth 64)
      (List.replicate n 0) (by simp; omega))
    simp only [List.length_replicate] at this
    rw [Proof.RsaPkcs1Sig.bytesAt_getD hi'] at this
    rw [this]; simp [hi']

/-- `copyBytes`: the `n` bytes at `src`, whatever they are in the run from
`σ` (`f σ`), copied to `dst`. -/
theorem copy_vp {src dst : BitVec 32} {n : Nat} (hd : WBuf L dst n) (hs : RBuf L src n)
    (hsep : Region.Disjoint ⟨src.setWidth 64, n⟩ ⟨dst.setWidth 64, n⟩) (hn : 0 < n)
    {Inv : State → Mem → Prop} (hI : ∀ σ m m', Inv σ m → Frame [⟨dst.setWidth 64, n⟩] m m' → Inv σ m')
    {f : State → Nat → Byte} :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ s.gpr .ebx = dst ∧ s.gpr .esi = src ∧
        s.gpr .ecx = BitVec.ofNat 32 n ∧ ∀ i < n, s.mem (byteAt src i) = f σ i)
      Impl.Bignum.X86.copyBytes
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ ∀ i < n, s.mem (byteAt dst i) = f σ i) := by
  have fit := hd.fit
  have fis := hs.fit
  refine VP.taint [.esi, .ebx, .ecx] copy_taint (fun _ _ _ _ h₁ h₂ r hr => ?_)
    fun σ s ⟨hc, hi, bx, si, cx, hf⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  have ctx : Proof.Bignum.X86.CopyCtx s src dst n :=
    ⟨hd.n32, fun i hi => by simp only [Proof.Bignum.X86.byteAddr]; rw [byte32 fis hi]; exact hs.inR hc.st hi,
      fun i hi => by simp only [Proof.Bignum.X86.byteAddr]; rw [byte32 fit hi]; exact hd.inW hc.st hi,
      fun i hi j hj e => by
        simp only [Proof.Bignum.X86.byteAddr] at e
        rw [byte32 fis hi, byte32 fit hj] at e
        exact hsep _ (contains_byte (Region.contains_self _ _) fis hi)
          (e ▸ contains_byte (Region.contains_self _ _) fit hj),
      fun i hi j hj e => byteAt_inj fit hi hj (by
        simp only [Proof.Bignum.X86.byteAddr] at e; rwa [byte32 fit hi, byte32 fit hj] at e)⟩
  refine WP.mono (Proof.Bignum.X86.copyBytes_ok s ctx hn si bx cx) fun t inv => ?_
  have fr : Frame [⟨dst.setWidth 64, n⟩] s.mem t.mem := frame_of_outside fit inv.outside
  refine ⟨hc.write fr (fun r hr => ?_) inv.rest.2.1 inv.rest.2.2 (inv.rest.1 .esp (by decide))
    (inv.rest.1 .ebp (by decide)), hI σ _ _ hi fr, fun i hi' => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hd.sub
  · have c := inv.copied i hi'
    simp only [Proof.Bignum.X86.byteAddr] at c
    rw [← byte32 fit hi', c, byte32 fis hi', hf i hi']

end VG.Proof.RsaPss.X86
