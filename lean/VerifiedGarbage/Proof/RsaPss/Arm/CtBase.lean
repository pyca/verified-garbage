module

public import VerifiedGarbage.Proof.RsaPss.CtPad
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytes
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytes
import VerifiedGarbage.Proof.Bignum.Arm.MaskBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytes
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Vp
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaPss.Arm.Step
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.RsaPss.Arm
public import VerifiedGarbage.Impl.MdHashTable.Arm
public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Hash
public import VerifiedGarbage.Spec.Mgf1

/-! ### `RsaPss.Arm.Hash`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS on ARMv7: what the proofs need of the hash function

ARMv7 has one implementation of each hash function, so RSASSA-PSS is
registered once per hash function, and its proofs are generic over a
`PssHash`: its code (`Impl.RsaPss.Arm.Hash`), what the proofs know of it as
a Merkle–Damgård hash function (`Proof.Pbkdf2.Md.Arm.HashOK`, with which HMAC
and PBKDF2 call its compression function), that its streaming code's length
field is right (`LenOk`, each hash function's `Shape.len`), the hash function
as RSA's padding takes it (`G`), the taint checks of its length field and
of the digest of a hash value (once for each hash function), and that MGF1's message `H ‖ C`
and its padding fit one block.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm
open VG.Proof.MdStream (Md)

/-- The length field code: from the byte count in `r4:r5`, the length field
at `r0 + N + B - L`, writing only `r9` (as `Shape.len`,
`Proof/MdStream/Arm/Common.lean`). -/
def LenOk {B N L : Nat} (md : Md B N L) (len : List Instr) : Prop :=
  ∀ s : State, (s.gpr .r0).toNat + (N + B) ≤ 2 ^ 32 →
    InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 (N + (B - L))) L →
    WP isa (.block len) s fun s' => (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (N + (B - L)))
        (md.lenOf (s.gpr .r5 ++ s.gpr .r4))

/-- A hash function, as RSASSA-PSS on ARMv7 uses it. -/
structure PssHash where
  /-- Its code. -/
  H : Impl.RsaPss.Arm.Hash
  /-- What the proofs know of its code as a Merkle–Damgård hash function. -/
  ok : Proof.Pbkdf2.Md.Arm.HashOK H.md
  /-- The length field. -/
  len : LenOk ok.md H.len
  lenAll : ∀ n, n < 2 ^ 32 → ok.md.lenOk n
  /-- The hash function as RSA's padding takes it. -/
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.SH.H.hash x
  glen : G.len = H.md.st.D
  /-- The taint checks of the digest of a hash value, a function of its
  table of `MdHash` (from the hash value at `r0` to `r1`,
  `Impl/MdHashTable/Arm.lean`), and of the length field (at `r0`). -/
  outCk : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1]) (Impl.MdHashTable.Arm.digest H.md.out)
    hc).isSome = true
  lenCk : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0]) (.block H.len) hc).isSome = true
  /-- MGF1's message `H ‖ C`, `0x80` and the length field fit one block. -/
  one : H.md.st.D + 5 + H.md.L ≤ H.md.st.B

/-- Its shape, all the code uses of it but its functions. -/
abbrev PssHash.sh (h : PssHash) : Impl.RsaPss.Arm.Sh := h.H.sh

end VG.Proof.RsaPss.Arm

end

end

/-! ### `RsaPss.Arm.Prims`, which this module and modules that import it used -/

section

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
    State.addr (p + BitVec.ofNat 32 i) = byteAt p i := addr_add (by omega_using [h, hi])

theorem contains_byte {R : Region} {p : BitVec 32} {n i : Nat} (hc : R.Contains (State.addr p) n)
    (fit : p.toNat + n ≤ 2 ^ 32) (hi : i < n) : R.Contains (byteAt p i) 1 :=
  hc.byte (by rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [fit, hi])]; exact hi)

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
  Classical.byContradiction fun hne => Offset.add_ofNat_ne (State.addr p) (a := i) (b := j) (by omega_using [h, hi]) (by omega_using [h, hj]) hne e

theorem frame_of_outside {p : BitVec 32} {n : Nat} {m m' : Mem} (h : p.toNat + n ≤ 2 ^ 32)
    (hm : ∀ a, (∀ j < n, a ≠ State.addr (p + BitVec.ofNat 32 j)) → m' a = m a) :
    Frame [⟨State.addr p, n⟩] m m' := by
  intro a ha
  refine hm a fun j hj e => ha _ (List.mem_singleton_self _) ?_
  rw [e, byte32 h hj]
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h, hj])]; omega_using [hj]

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
    · simp only [Region.Contains] at ha; omega_using [ha]
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
    · simp only [Region.Contains] at ha; omega_using [ha]
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

namespace Sg

theorem rdS {L : Lay} (m : Mem) (v : BitVec 32) {d : Nat} (hd : d + 4 ≤ 64) :
    (m.writeW (L.fr d) v).readW (L.fr sS) 32 = m.readW (L.fr sS) 32 :=
  Lay.readW_fr_other L m v (by unfold sS; omega_arith) (by decide) (by omega_arith)

/-- Words written to the frame from slot `k` on. -/
def wl (L : Lay) : Mem → Nat → List (BitVec 32) → Mem
  | m, _, [] => m
  | m, k, v :: vs => wl L (m.writeW (L.fr (4 * k)) v) (k + 1) vs

theorem wl_nil (L : Lay) (m : Mem) (k : Nat) : wl L m k [] = m := rfl
theorem wl_cons (L : Lay) (m : Mem) (k : Nat) (v : BitVec 32) (vs : List (BitVec 32)) :
    wl L m k (v :: vs) = wl L (m.writeW (L.fr (4 * k)) v) (k + 1) vs := rfl

theorem wl_other (L : Lay) : ∀ (vs : List (BitVec 32)) (m : Mem) (k j : Nat), j < k → k + vs.length ≤ 16 →
    (wl L m k vs).readW (L.fr (4 * j)) 32 = m.readW (L.fr (4 * j)) 32
  | [], _, _, _, _, _ => rfl
  | v :: vs, m, k, j, hj, hl => by
    rw [wl_cons, wl_other L vs _ (k + 1) j (by omega_arith) (by simp at hl; omega_arith),
      Lay.readW_fr_other _ _ _ (by omega_arith) (by omega_arith) (by simp at hl; omega_arith)]

theorem wl_read (L : Lay) : ∀ (vs : List (BitVec 32)) (m : Mem) (k i : Nat), k ≤ i → i < k + vs.length →
    k + vs.length ≤ 16 → (wl L m k vs).readW (L.fr (4 * i)) 32 = vs.getD (i - k) 0
  | [], _, _, _, h₁, h₂, _ => by simp at h₂; omega_arith
  | v :: vs, m, k, i, h₁, h₂, hl => by
    rw [wl_cons]
    simp only [List.length_cons] at h₂ hl
    by_cases e : i = k
    · subst e
      rw [wl_other L vs _ (i + 1) i (by omega_arith) (by omega_arith), Mem.readW_writeW_self32, Nat.sub_self]; rfl
    · rw [wl_read L vs _ (k + 1) i (by omega_arith) (by omega_arith) (by omega_arith), show i - k = (i - (k + 1)) + 1 by omega_arith]; rfl

theorem wl_frame (L : Lay) : ∀ (vs : List (BitVec 32)) (m : Mem) (k : Nat), k + vs.length ≤ 16 →
    Frame [⟨L.fr 0, 64⟩] m (wl L m k vs)
  | [], _, _, _ => Frame.refl _ _
  | v :: vs, m, k, hl => by
    rw [wl_cons]
    simp only [List.length_cons] at hl
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (Nat.zero_le _) (by omega_arith) (by omega_arith))).trans (wl_frame L vs _ (k + 1) (by omega_arith))

end Sg

end VG.Proof.RsaPss.Arm

end

end

/-!
# RSASSA-PSS on ARMv7: hashing a message of secret length, the setting

The hash function's sizes (`PssHash.B`, …); ranges of our part of
`scratch` as buffers (`Geo.wbuf`); facts about memory that writes elsewhere
keep (`slot_keep`); and the bytes of `Y` after the padding
loop (`padY`), which are the padded message over its blocks (`padY_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.MdStream (Md)

namespace PssHash

variable (h : PssHash)

abbrev B : Nat := h.H.md.st.B
abbrev D : Nat := h.H.md.st.D
abbrev N : Nat := h.H.md.N
abbrev L : Nat := h.H.md.L

abbrev md : Md h.B h.N h.L := h.ok.md

theorem B_cases : h.B = 64 ∨ h.B = 128 := h.ok.sizes.B
theorem N_le : h.N ≤ 64 := h.ok.sizes.N64
theorem L_le : h.L ≤ 16 := h.ok.sizes.L16
theorem D_le : h.D ≤ h.N := h.ok.sizes.DN
theorem D_pos : 0 < h.D := h.ok.sizes.D0
theorem NL : h.N + h.L ≤ h.B := h.ok.sizes.NL
theorem so_le : h.H.md.so ≤ 512 := by have := h.ok.sizes.so; have := h.ok.sizes.W; omega_arith
theorem B_le : h.B ≤ 128 := by rcases h.B_cases with e | e <;> omega_using [e]
theorem B_ge : 64 ≤ h.B := by rcases h.B_cases with e | e <;> omega_using [e]
theorem S_eq : h.H.md.st.S = h.N + h.B := h.ok.sizes.S

theorem lg : lgB h.sh = 6 ∧ h.B = 64 ∨ lgB h.sh = 7 ∧ h.B = 128 := by
  unfold lgB
  rcases h.B_cases with e | e
  · exact .inl ⟨by show Nat.log2 h.B = 6; rw [e]; decide, e⟩
  · exact .inr ⟨by show Nat.log2 h.B = 7; rw [e]; decide, e⟩

theorem pow_lg : 2 ^ lgB h.sh = h.B := by rcases h.lg with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b] <;> rfl

theorem lg_range : 1 ≤ lgB h.sh ∧ lgB h.sh ≤ 31 := by rcases h.lg with ⟨a, _⟩ | ⟨a, _⟩ <;> rw [a] <;> decide

end PssHash

/-- `omega`, with the offsets of our part of `scratch` and of the frame as
numbers, and the hash function's sizes in one form. -/
macro "pomega" : tactic => `(tactic| (have _ : VG.Impl.RsaPss.Arm.oCW = 4096 := rfl; have _ : VG.Impl.RsaPss.Arm.oSt = 4608 := rfl; have _ : VG.Impl.RsaPss.Arm.oSel = 4864 := rfl; have _ : VG.Impl.RsaPss.Arm.oDig = 4928 := rfl; have _ : VG.Impl.RsaPss.Arm.oLen = 4992 := rfl; have _ : VG.Impl.RsaPss.Arm.oEm = 0 := rfl; have _ : VG.Impl.RsaPss.Arm.oY = 1024 := rfl; have _ : VG.Impl.RsaPss.Arm.oRsa = 8192 := rfl; have _ : VG.Impl.RsaPss.Arm.frameBytes = 128 := rfl; (try simp only [VG.Impl.RsaPss.Arm.blk, VG.Impl.RsaPss.Arm.dig, VG.Impl.RsaPss.Arm.hvN, VG.Impl.RsaPss.Arm.lenL, VG.Proof.RsaPss.Arm.PssHash.sh, VG.Impl.RsaPss.Arm.Hash.sh, VG.Impl.Pbkdf2.Md.Arm.Hash.B, VG.Impl.Pbkdf2.Md.Arm.Hash.D, VG.Proof.RsaPss.Arm.PssHash.B, VG.Proof.RsaPss.Arm.PssHash.D, VG.Proof.RsaPss.Arm.PssHash.N, VG.Proof.RsaPss.Arm.PssHash.L] at *); omega))

variable {L : Lay} {scr : BitVec 32}

namespace Geo

variable (hg : Geo L scr)
include hg

theorem scr_lt {o : Nat} (h : o ≤ oRsa) : (scr + BitVec.ofNat 32 o).toNat = scr.toNat + o := by
  have := hg.fit; unfold oRsa at *
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [h]), Nat.mod_eq_of_lt (by omega_using [h, this])]

theorem byteAt_scr {o i : Nat} (h : o + i < oRsa) : byteAt (scr + BitVec.ofNat 32 o) i = sa scr (o + i) := by
  rw [byteAt, hg.addr (by omega_using [h]), sa, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- A range of our part of `scratch`, as a buffer the body writes. -/
theorem wbuf {o n : Nat} (h : o + n ≤ oRsa) (hn : 0 < n) : WBuf L (scr + BitVec.ofNat 32 o) n := by
  obtain ⟨σ, ok⟩ := hg.ok
  obtain ⟨k, hk, hR⟩ := hg.sub
  have fit := hg.fit
  unfold oRsa at h hk fit
  refine ⟨by rw [hg.scr_lt (by unfold oRsa; omega_using [h])]; omega_using [h, fit], by omega_using [h], ⟨_, List.mem_cons_of_mem _ hR, ?_⟩, ?_⟩
  · rw [hg.addr (by unfold oRsa; omega_using [h, hn])]
    exact Offset.contains_base _ (by omega_using [h, hk]) (by omega_using [h])
  · rw [hg.addr (by unfold oRsa; omega_using [h, hn])]
    exact hg.slot ok (o := o) (n := n) (by unfold oRsa; omega_using [h]) (by rw [hg.F]; decide)

theorem rbuf {o n : Nat} (h : o + n ≤ oRsa) (hn : 0 < n) : RBuf L (scr + BitVec.ofNat 32 o) n := (hg.wbuf h hn).rbuf

end Geo

/-! ## Facts that writes elsewhere keep -/

theorem slot_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {d : Nat} {v : BitVec 32}
    (hd : ∀ r ∈ rs, (slotR L d).Disjoint r) (h : m.readW (L.fr d) 32 = v) : m'.readW (L.fr d) 32 = v := by
  rw [hf.readW (r := slotR L d) (Region.contains_self _ _) hd (by decide)]; exact h

/-- A byte of our part of `scratch` after a byte is written there. -/
theorem sa_write (scr : BitVec 32) (m : Mem) {o i : Nat} (b : Byte) (ho : o < 2 ^ 64) (hi : i < 2 ^ 64) :
    (m.writeW (sa scr o) b) (sa scr i) = if i = o then b else m (sa scr i) := by
  rw [VG.WriteBytes.writeW8_apply]
  by_cases e : i = o
  · subst e; simp
  · rw [ite_eq_right (Offset.add_ofNat_ne _ hi ho e), ite_eq_right e]

/-- A byte written within a range of our part of `scratch`. -/
theorem frame_byte (scr : BitVec 32) (m : Mem) {o n x : Nat} (b : Byte) (h₁ : o ≤ x) (h₂ : x < o + n)
    (hn : o + n < 2 ^ 64) : Frame [sR scr o n] m (m.writeW (sa scr x) b) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [hn]))

/-- Bytes of our part of `scratch` kept by writes elsewhere. -/
theorem sbytes_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (sR scr o n) r) (hn : o + n < 2 ^ 64) {f : Nat → Byte}
    (h : ∀ i < n, m (sa scr (o + i)) = f i) : ∀ i < n, m' (sa scr (o + i)) = f i := fun i hi => by
  rw [← h i hi]
  refine hf _ fun r hr hc => hd r hr _ (Offset.contains _ (Nat.le_add_right _ _) (by omega_using [hi]) (by omega_using [hn])) hc

/-- A hash value kept by writes elsewhere. -/
theorem stateAt_keep (h : PssHash) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (sR scr o h.N) r) : h.md.stateAt m' (sa scr o) = h.md.stateAt m (sa scr o) :=
  h.md.stateAt_congr fun _ hi => hf.bytes (R := sR scr o h.N) hd (by show h.N ≤ 2 ^ 64; have := h.N_le; omega_using [this]) hi

/-- A frame within a sub-list of regions. -/
theorem Frame.subset {rs rs' : List Region} {m m' : Mem} (h : Frame rs m m') (hs : ∀ r ∈ rs, r ∈ rs') :
    Frame rs' m m' := h.mono hs

/-! ## The padded message in `Y` -/

/-- Byte `j` of the block at `oLen`: zeros, then the length field `lenB`. -/
def lenBlk (B L : Nat) (lenB : List Byte) (j : Nat) : Byte :=
  if j < B - L then 0 else lenB.getD (j - (B - L)) 0

/-- Byte `i` of `Y` after the padding loop, for the message `msg` followed by
zeros: `0x80` ORed into byte `ℓ`, and the block at `oLen` into the last
block of the padded message. -/
def padY (B L : Nat) (msg lenB : List Byte) (i : Nat) : Byte :=
  msg.getD i 0 ||| (if i = msg.length then 0x80 else 0) |||
    (if i / B = (msg.length + L) / B then lenBlk B L lenB (i % B) else 0)

theorem or_zero (x : Byte) : x ||| 0 = x := by revert x; decide
theorem zero_or (x : Byte) : 0 ||| x = x := by revert x; decide

theorem getD_ge {l : List Byte} {i : Nat} (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- Over the blocks of the padded message, `padY` is the padded message. -/
theorem padY_eq {B L : Nat} (hB : 0 < B) (hLB : L < B) (msg lenB : List Byte) {i : Nat}
    (hi : i < B * ((msg.length + L) / B + 1)) :
    padY B L msg lenB i = RsaPss.padded B L msg lenB i := by
  have hlt := Nat.lt_mul_div_succ (msg.length + L) hB
  have hge := Nat.mul_div_le (msg.length + L) B
  generalize hfb : (msg.length + L) / B = fb at hlt hge hi
  have hdiv : i / B ≤ fb := by
    have := (Nat.div_lt_iff_lt_mul hB).mpr (show i < (fb + 1) * B by rw [Nat.mul_comm]; exact hi)
    omega_using [this]
  have hmod := Nat.div_add_mod i B
  have hmodl := Nat.mod_lt i hB
  have e2 : B * (fb + 1) = B * fb + B := Nat.mul_succ _ _
  rw [Nat.mul_comm] at hge
  simp only [padY, RsaPss.padded, RsaPss.lastBlk, hfb, lenBlk]
  by_cases h1 : i < msg.length
  · rw [ite_eq_left h1, ite_eq_right (by omega_using [h1])]
    by_cases h3 : i / B = fb
    · have e1 : B * (i / B) = B * fb := by rw [h3]
      rw [ite_eq_left h3, ite_eq_left (by omega_using [hB, hLB, hfb, hlt, hge, hi, hdiv, hmod, hmodl, e2, h1, h3, e1]), or_zero, or_zero]
    · rw [ite_eq_right h3, or_zero, or_zero]
  · rw [ite_eq_right h1, getD_ge (by omega_using [h1]), zero_or]
    by_cases h2 : i = msg.length
    · rw [ite_eq_left h2, ite_eq_left h2]
      by_cases h3 : i / B = fb
      · have e1 : B * (i / B) = B * fb := by rw [h3]
        rw [ite_eq_left h3, ite_eq_left (by omega_using [hB, hLB, hfb, hlt, hge, hi, hdiv, hmod, hmodl, e2, h1, h2, h3, e1]), or_zero]
      · rw [ite_eq_right h3, or_zero]
    · rw [ite_eq_right h2, ite_eq_right h2, zero_or]
      by_cases h3 : i / B = fb
      · rw [ite_eq_left h3]
        have e1 : B * (i / B) = B * fb := by rw [h3]
        have hm : i % B = i - B * fb := by omega_using [hB, hLB, hfb, hlt, hge, hi, hdiv, hmod, hmodl, e2, h1, h2, h3, e1]
        by_cases h4 : B * fb + B - L ≤ i ∧ i < B * fb + B
        · rw [ite_eq_right (by omega_using [hB, hLB, hfb, hlt, hge, hi, hdiv, hmod, hmodl, e2, h1, h2, h3, e1, hm, h4]), ite_eq_left h4]
          congr 1; omega_using [hB, hLB, hfb, hlt, hge, hi, hdiv, hmod, hmodl, e2, h1, h2, h3, e1, hm, h4]
        · rw [ite_eq_right h4, ite_eq_left (by omega_using [hB, hLB, hfb, hlt, hge, hi, hdiv, hmod, hmodl, e2, h1, h2, h3, e1, hm, h4])]
      · rw [ite_eq_right h3, ite_eq_right (by
          intro ⟨h5, _⟩
          exact h3 (Nat.le_antisymm hdiv ((Nat.le_div_iff_mul_le hB).mpr (by rw [Nat.mul_comm]; omega_arith))))]

end VG.Proof.RsaPss.Arm
