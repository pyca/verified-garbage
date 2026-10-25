module

public import VerifiedGarbage.Proof.ChaCha20.Stream
meta import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.ChaCha20.StreamBytes
meta import VerifiedGarbage.Proof.ChaCha20.StreamBytes
public import VerifiedGarbage.Impl.ChaCha20.RISCV64.Stream
meta import VerifiedGarbage.Impl.ChaCha20.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# Streaming ChaCha20 on RISC-V: `init` and `set_nonce`

Untrusted: everything here is checked by Lean. The structure of the PPC64LE
proof (`Proof/ChaCha20/PPC64LE/Stream/Init.lean`), with the state written a
byte at a time (`Proof/Framework/RISCV64/Bytes.lean`): `set_nonce` leaves
the constants, the key and the nonce byte by byte, which
`VG.Proof.ChaCha20.stream_of_parts` turns into the keystream.
-/

@[expose] public section

namespace VG.Proof.ChaCha20

open VG.RISCV64
open VG.Spec.ChaCha20 (keyAt restAt keystreamOf bytesAt leftAt)

/-- RISC-V contract for `vg_chacha20_set_nonce(state = a0, nonce = a1)`. -/
def setNonceRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 768⟩
    let nonce : Region := ⟨s.gpr .a1, 16⟩
    s.rd = [nonce] ∧ s.wr = [state] ∧ state.Disjoint nonce
  post s s' :=
    keyAt s'.mem (s.gpr .a0) = keyAt s.mem (s.gpr .a0) ∧
      restAt s'.mem (s.gpr .a0) = keystreamOf (keyAt s.mem (s.gpr .a0)) (bytesAt s.mem (s.gpr .a1) 16)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

/-- RISC-V contract for `vg_chacha20_init(state = a0, key = a1, nonce = a2)`. -/
def initRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 768⟩
    let key : Region := ⟨s.gpr .a1, 32⟩
    let nonce : Region := ⟨s.gpr .a2, 16⟩
    s.rd = [key, nonce] ∧ s.wr = [state] ∧ state.Disjoint key ∧ state.Disjoint nonce
  post s s' :=
    keyAt s'.mem (s.gpr .a0) = bytesAt s.mem (s.gpr .a1) 32 ∧
      restAt s'.mem (s.gpr .a0) = keystreamOf (bytesAt s.mem (s.gpr .a1) 32) (bytesAt s.mem (s.gpr .a2) 16)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.RISCV64.Stream

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Bytes VG.RISCV64.ByteLoad
  VG.Impl.ChaCha20.RISCV64.Stream VG.Impl.Words.RISCV64
open VG.Spec.ChaCha20 (keyAt restAt keystreamOf bytesAt leftAt wordLE)

/-- No instruction of the code writes a callee-saved register or `ra`. -/
theorem keeps {c : Prog isa}
    (hc : ((instrs c).all fun i => (Reg.ra :: preserved).all fun r => dstOf i != some r) = true)
    {s s' : State} {t : List Leak} (he : Exec isa c s t s') (hn : c.noCalls = true := by decide +kernel) :
    ∀ r ∈ Reg.ra :: preserved, s'.gpr r = s.gpr r := fun r hr =>
  Exec.gpr (fun i hi => by simpa using List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr) he (.inl hn)

theorem abi_of_keeps {c : Prog isa}
    (hc : ((instrs c).all fun i => (Reg.ra :: preserved).all fun r => dstOf i != some r) = true)
    {s s' : State} {t : List Leak} (he : Exec isa c s t s') (hn : c.noCalls = true := by decide +kernel) :
    abiPreserved s s' :=
  ⟨fun r hr => keeps hc he hn r (List.mem_cons_of_mem _ hr), Exec.sp he,
    keeps hc he hn _ (List.mem_cons_self ..)⟩

/-- The constants, byte by byte. -/
theorem sigmaBytes_eq : ∀ i < 16, BitVec.ofNat 8 (sigmaBytes.getD i 0) = sigma.getD i 0 := by decide

theorem sigmaBytes_lt : ∀ i < sigmaBytes.length, sigmaBytes.getD i 0 < 2048 := by decide

theorem sigmaBytes_length : sigmaBytes.length = 16 := rfl

/-- The bytes left, as the code computes them. -/
def leftW (c : BitVec 64) : BitVec 64 := (BitVec.ofNat 64 1 <<< 32 - c) <<< 6

/-- `64 × (2³² − c)`. -/
theorem leftW_eq (c : BitVec 32) :
    leftW (c.setWidth 64) = BitVec.ofNat 64 (64 * (2 ^ 32 - c.toNat)) := by
  have hc := c.isLt
  have h0 : BitVec.ofNat 64 1 <<< 32 - c.setWidth 64 = BitVec.ofNat 64 (2 ^ 32 - c.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [show BitVec.ofNat 64 1 <<< 32 = BitVec.ofNat 64 (2 ^ 32) by decide, BitVec.toNat_sub,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [leftW, h0]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The low word of a number. -/
theorem lo_ofNat (x : Nat) : (BitVec.ofNat 64 x).setWidth 32 = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_mod_of_dvd x (by decide : 2 ^ 32 ∣ 2 ^ 64)]

/-- The high word of a number. -/
theorem hi_ofNat {x : Nat} (h : x < 2 ^ 64) :
    (BitVec.ofNat 64 x >>> 32).setWidth 32 = BitVec.ofNat 32 (x / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- A number below 2⁶⁴, stored by `storeLE64` at byte 128: the bytes left. -/
theorem leftAt_store (m : Mem) (p : Addr) {x : Nat} (h : x < 2 ^ 64) :
    leftAt ((m.writeW (p + BitVec.ofNat 64 128) ((BitVec.ofNat 64 x).setWidth 32)).writeW
      (p + BitVec.ofNat 64 (128 + 4)) ((BitVec.ofNat 64 x >>> 32).setWidth 32)) p = x := by
  rw [lo_ofNat, hi_ofNat h]
  exact leftAt_halves m p h

/-- What `set_nonce` needs of the state it runs from. -/
structure NPre (s : State) (st np : Addr) : Prop where
  a0 : s.gpr .a0 = st
  a1 : s.gpr .a1 = np
  w_st : ∀ d n, d + n ≤ 768 → InRegions s.wr (st + BitVec.ofNat 64 d) n
  r_n : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (np + BitVec.ofNat 64 d) n
  dj : (⟨st, 768⟩ : Region).Disjoint ⟨np, 16⟩

/-- The memory `set_nonce` leaves, from `m`, byte by byte. -/
structure NPost (m : Mem) (st np : Addr) (m' : Mem) : Prop where
  sigma : ∀ i < 16, m' (st + BitVec.ofNat 64 i) = sigma.getD i 0
  key : ∀ i < 32, m' (st + BitVec.ofNat 64 (16 + i)) = m (st + BitVec.ofNat 64 (16 + i))
  nonce : ∀ i < 16, m' (st + BitVec.ofNat 64 (48 + i)) = m (np + BitVec.ofNat 64 i)
  left : leftAt m' st = 64 * (2 ^ 32 - (m.readW np 32).toNat)
  frame : Frame [⟨st, 768⟩] m m'

theorem contains_st (st : Addr) {d n : Nat} (hd : d + n ≤ 768) :
    (⟨st, 768⟩ : Region).Contains (st + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ hd (by omega)

/-- A byte of the state outside a sub-range written. -/
theorem byte_frame {m m' : Mem} {st : Addr} {e k i : Nat} (hf : Frame [⟨st + BitVec.ofNat 64 e, k⟩] m m')
    (h : i + 1 ≤ e ∨ e + k ≤ i) (hi : i < 768) (he : e + k ≤ 768) :
    m' (st + BitVec.ofNat 64 i) = m (st + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint st h (by omega) (by omega) _ (Region.contains_self _ _) hc

theorem setNonce_exec {s : State} {st np : Addr} (hp : NPre s st np) :
    WP isa setNonce s fun s' => NPost s.mem st np s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have sub_st : ∀ {d n}, d + n ≤ 768 → Region.Sub ⟨st + BitVec.ofNat 64 d, n⟩ ⟨st, 768⟩ :=
    fun h => Offset.sub_base _ h
  unfold setNonce setNonceInstrs
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  -- The nonce into words 12–15.
  refine WP.mono (copyBytes_ok (tmp := .t1) (src := .a1) (dst := .a0) (soff := 0) (doff := 48)
    (n := 16) (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by rw [hp.a1]; exact hp.r_n _ 1 (by omega))
    (fun i hi => by rw [hp.a0]; exact hp.w_st _ 1 (by omega))
    (fun i hi hc => by
      rw [hp.a0, hp.a1] at hc
      exact hp.dj _ (sub_st (by omega) _ hc) (Offset.contains_base _ (by omega) (by omega))))
    fun s₁ h₁ => ?_
  have a0₁ : s₁.gpr .a0 = st := by rw [h₁.gpr _ (by decide), hp.a0]
  have a1₁ : s₁.gpr .a1 = np := by rw [h₁.gpr _ (by decide), hp.a1]
  have c₁ : ∀ j < 16, s₁.mem (st + BitVec.ofNat 64 (48 + j)) = s.mem (np + BitVec.ofNat 64 (0 + j)) := by
    rw [← hp.a0, ← hp.a1]; exact h₁.copied
  have f₁ : Frame [⟨st + BitVec.ofNat 64 48, 16⟩] s.mem s₁.mem := by rw [← hp.a0]; exact h₁.frame
  rw [WP.block_append_iff]
  -- The constants into words 0–3.
  refine WP.mono (storeBytes_ok (tmp := .t1) (dst := .a0) (doff := 0) (bs := sigmaBytes) (by decide)
    sigmaBytes_lt (by decide) (fun i hi => by rw [a0₁, h₁.wr]; exact hp.w_st _ 1 (by
      rw [sigmaBytes_length] at hi; omega))) fun s₂ h₂ => ?_
  have c₂ : ∀ j < 16, s₂.mem (st + BitVec.ofNat 64 (0 + j)) = BitVec.ofNat 8 (sigmaBytes.getD j 0) := by
    rw [← a0₁]; exact h₂.stored
  have f₂' : Frame [⟨st + BitVec.ofNat 64 0, 16⟩] s₁.mem s₂.mem := by rw [← a0₁]; exact h₂.frame
  have a0₂ : s₂.gpr .a0 = st := by rw [h₂.gpr _ (by decide), a0₁]
  have a1₂ : s₂.gpr .a1 = np := by rw [h₂.gpr _ (by decide), a1₁]
  have f₂ : Frame [⟨st, 768⟩] s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sub_st (by omega)⟩).trans
    (f₂'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sub_st (by omega)⟩)
  rw [WP.block_append_iff]
  -- The initial block counter.
  refine WP.mono (loadLE32_ok (d := .t1) (tmp := .t2) (n := .a1) (off := 0) (by decide) (by decide) (by decide)
    (by decide) (by rw [a1₂, h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hp.r_n 0 4 (by decide))) fun s₃ e₃ => ?_
  have hc : s₂.mem.readW (np + BitVec.ofNat 64 0) 32 = s.mem.readW np 32 := by
    rw [f₂.readW (r := ⟨np, 16⟩) (Offset.contains_base _ (by omega) (by omega)) (by simpa using hp.dj.symm)
      (by decide)]
    simp
  rw [WP.block_append_iff]
  refine wp_li (imm := 1) (by decide) fun s₄ u₄ => wp_sll (by decide) fun s₅ u₅ => wp_sub fun s₆ u₆ =>
    wp_sll (by decide) fun s₇ u₇ => WP.block_nil ?_
  have t₇ : s₇.gpr .t2 = BitVec.ofNat 64 (64 * (2 ^ 32 - (s.mem.readW np 32).toNat)) := by
    rw [u₇.gpr, u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₄.other _ (by decide), e₃,
      RegUpd.gpr_write_self, a1₂, hc, ← leftW_eq]
    rfl
  have a0₇ : s₇.gpr .a0 = st := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), e₃,
      RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), a0₂]
  have m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, e₃]; rfl
  have rd₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, e₃]; exact h₂.rd.trans h₁.rd
  have wr₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, e₃]; exact h₂.wr.trans h₁.wr
  -- The bytes left.
  refine WP.mono (storeLE64_ok (v := .t2) (tmp := .t1) (hi := .t3) (n := .a0) (off := 128) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [a0₇, wr₇]; exact hp.w_st 128 4 (by decide)) (by rw [a0₇, wr₇]; exact hp.w_st 132 4 (by decide)))
    fun s₈ ⟨m₈, _, rd₈, wr₈, _⟩ => ⟨?_, rd₈.trans rd₇, wr₈.trans wr₇⟩
  have hN : 64 * (2 ^ 32 - (s.mem.readW np 32).toNat) < 2 ^ 64 := by
    have := (s.mem.readW np 32).isLt; omega
  rw [a0₇, t₇, m₇] at m₈
  have hf₈ : Frame [⟨st + BitVec.ofNat 64 128, 8⟩] s₂.mem s₈.mem := by
    rw [m₈]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega)
      (by omega))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  have k₈ : ∀ i < 128, s₈.mem (st + BitVec.ofNat 64 i) = s₂.mem (st + BitVec.ofNat 64 i) :=
    fun i hi => byte_frame hf₈ (by omega) (by omega) (by omega)
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_⟩
  · rw [k₈ i (by omega), ← sigmaBytes_eq i hi, ← c₂ i hi, Nat.zero_add]
  · rw [k₈ _ (by omega), byte_frame f₂' (by omega) (by omega) (by omega),
      byte_frame f₁ (by omega) (by omega) (by omega)]
  · rw [k₈ _ (by omega), byte_frame f₂' (by omega) (by omega) (by omega), c₁ i hi, Nat.zero_add]
  · rw [m₈]; exact leftAt_store _ _ hN
  · exact f₂.trans (hf₈.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sub_st (by omega)⟩)

/-- What `set_nonce` leaves: the key kept, and the whole keystream of the
nonce. -/
theorem NPost.post {m : Mem} {st np : Addr} {m' : Mem} (h : NPost m st np m') :
    keyAt m' st = keyAt m st ∧ restAt m' st = keystreamOf (keyAt m st) (bytesAt m np 16) := by
  refine stream_of_parts (by simp [keyAt, length_bytesAt]) h.sigma (fun i hi => ?_) (fun i hi => ?_) ?_
  · rw [h.key i hi, keyAt, show (st + 16 : Addr) = st + BitVec.ofNat 64 16 from rfl, bytesAt_getD _ _ hi,
      Offset.add_add]
  · rw [h.nonce i hi, bytesAt_getD _ _ hi]
  · rw [h.left, wordLE_bytesAt _ _ (by decide)]

theorem setNonce_ok (s : State) (hs : Proof.ChaCha20.setNonceRISCV64.pre s) :
    ∃ t s', Exec isa setNonce s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.setNonceRISCV64.post s s' := by
  obtain ⟨hrd, hwr, hdj⟩ := hs
  have hp : NPre s (s.gpr .a0) (s.gpr .a1) :=
    ⟨rfl, rfl, fun d n hd => ⟨_, by rw [hwr]; exact List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩,
      fun d n hd => ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
        Offset.contains_base _ hd (by omega)⟩, hdj⟩
  obtain ⟨t, s', he, hm, -, -⟩ := setNonce_exec hp
  exact ⟨t, s', he, abi_of_keeps (by rw [← Code.allInstrs_eq]; decide +kernel) he, hm.post⟩

theorem setNonce_ct :
    ConstantTime isa Proof.ChaCha20.setNonceRISCV64.pre Proof.ChaCha20.setNonceRISCV64.pub setNonce := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h1, h2]

/-- A state satisfying the precondition of `set_nonce`. -/
def setNonceSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 16⟩]
  wr := [⟨0x1000, 768⟩]

theorem setNonce_verified :
    Verified RISCV64.target setNonce (Spec.ChaCha20.setNonceContract RISCV64.abi) :=
  Verified.of_correct setNonce_ok setNonce_ct (by
    sig_implies [Spec.ChaCha20.setNonceContract, Spec.ChaCha20.setNonceSig,
      Proof.ChaCha20.setNonceRISCV64, RISCV64.abi, RISCV64.argRegs] [setNonceSat] using setNonceSat)

/-! ## `init` -/

theorem init_eq : init = .block (keyInstrs ++ setNonceInstrs) := rfl

theorem init_ok (s : State) (hs : Proof.ChaCha20.initRISCV64.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.initRISCV64.post s s' := by
  obtain ⟨hrd, hwr, hdk, hdn⟩ := hs
  have hw : ∀ d n, d + n ≤ 768 → InRegions s.wr (s.gpr .a0 + BitVec.ofNat 64 d) n :=
    fun d n hd => ⟨_, by rw [hwr]; exact List.mem_singleton_self _, Offset.contains_base _ hd (by omega)⟩
  obtain ⟨t, s', he, m₁, hm, hk₁, hn₁⟩ : WP isa init s fun s' => ∃ m₁ : Mem,
      NPost m₁ (s.gpr .a0) (s.gpr .a2) s'.mem ∧
      (∀ i < 32, m₁ (s.gpr .a0 + BitVec.ofNat 64 (16 + i)) = s.mem (s.gpr .a1 + BitVec.ofNat 64 i)) ∧
      ∀ x, (⟨s.gpr .a2, 16⟩ : Region).Contains x 1 → m₁ x = s.mem x := by
    rw [init_eq, keyInstrs, List.append_assoc, WP.block_append_iff]
    refine WP.mono (copyBytes_ok (tmp := .t1) (src := .a1) (dst := .a0) (soff := 0) (doff := 16) (n := 32)
      (by decide) (by decide) (by decide) (by decide)
      (fun i hi => ⟨⟨s.gpr .a1, 32⟩, by rw [hrd]; simp, Offset.contains_base _ (by omega) (by omega)⟩)
      (fun i hi => hw _ 1 (by omega))
      (fun i hi hc => hdk _ (Offset.sub_base _ (by omega) _ hc) (Offset.contains_base _ (by omega) (by omega))))
      fun s₁ h₁ => ?_
    refine wp_mv fun s₂ u₂ => ?_
    have hp : NPre s₂ (s.gpr .a0) (s.gpr .a2) :=
      ⟨by rw [u₂.other _ (by decide), h₁.gpr _ (by decide)], by rw [u₂.gpr, h₁.gpr _ (by decide)],
        fun d n hd => by rw [u₂.wr, h₁.wr]; exact hw d n hd,
        fun d n hd => ⟨⟨s.gpr .a2, 16⟩, by rw [u₂.rd, u₂.wr, h₁.rd, h₁.wr, hrd]; simp,
          Offset.contains_base _ hd (by omega)⟩, hdn⟩
    refine WP.mono (setNonce_exec hp) fun s' ⟨h', _, _⟩ => ⟨s₂.mem, h', fun i hi => ?_, fun x hx => ?_⟩
    · rw [u₂.mem, h₁.copied i hi, Nat.zero_add]
    · rw [u₂.mem]
      exact h₁.frame _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdn _ (Offset.sub_base _ (by omega) _ hc) hx
  refine ⟨t, s', he, abi_of_keeps (by rw [← Code.allInstrs_eq]; decide +kernel) he, ?_⟩
  obtain ⟨hk, hr⟩ := hm.post
  have hkey : keyAt m₁ (s.gpr .a0) = bytesAt s.mem (s.gpr .a1) 32 := by
    refine (keyAt_of_bytes (by simp [length_bytesAt]) fun i hi => ?_)
    rw [hk₁ i hi, bytesAt_getD _ _ hi]
  have hn : bytesAt m₁ (s.gpr .a2) 16 = bytesAt s.mem (s.gpr .a2) 16 :=
    List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi
      exact hn₁ _ (Offset.contains_base _ (by omega) (by omega))
  simp only [Proof.ChaCha20.initRISCV64]
  rw [hk, hr, hkey, hn]
  exact ⟨rfl, rfl⟩

theorem init_ct : ConstantTime isa Proof.ChaCha20.initRISCV64.pre Proof.ChaCha20.initRISCV64.pub init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h1, h2, h3]

/-- A state satisfying the precondition of `init`. -/
def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x1000, 768⟩]

theorem init_verified : Verified RISCV64.target init (Spec.ChaCha20.initContract RISCV64.abi) :=
  Verified.of_correct init_ok init_ct (by
    sig_implies [Spec.ChaCha20.initContract, Spec.ChaCha20.initSig, Proof.ChaCha20.initRISCV64,
      RISCV64.abi, RISCV64.argRegs] [initSat] using initSat)

end VG.Proof.ChaCha20.RISCV64.Stream
