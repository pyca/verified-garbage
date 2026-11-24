module

public import VerifiedGarbage.Impl.Camellia.X86.AesNiExpandKey
meta import VerifiedGarbage.Impl.Camellia.X86.AesNiExpandKey
public import VerifiedGarbage.Proof.Camellia.X86.AesNiCore
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiMaps
meta import VerifiedGarbage.Proof.Framework.X86.ByteMap
public import VerifiedGarbage.Proof.Camellia.X86.ExpandKey
meta import VerifiedGarbage.Proof.Camellia.X86.ExpandKey
meta import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Camellia.X86.AesNiKeyLit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiKeyLit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel

/-!
# Camellia's key schedule on x86 (32-bit), its rounds by `aesenclast`

`mid_ok`: the block for `KA` and `KB` (`Impl/Camellia/X86/AesNiExpandKey.lean`)
leaves what the key schedule's proof (`ExpandKey.lean`) needs. `pairX_wp`: a pair of rounds on the value in `xmm0` is the
specification's, with the last pair of a group of the one-block code
(`lastpair_wp`, `AesNiCore.lean`) between the conversions, under the keys
`keysIn` copies, which the kernel checks are those of the constants
(`sig_all`); `kaKb_wp` composes three.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.AesNiKey

open VG VG.X86 VG.X86.ByteMap VG.Impl.Camellia.X86.AesNi VG.Impl.Camellia.X86.AesNiKey
open VG.Proof.Camellia.X86.AesNi
open VG.Impl.Aes.X86 (sb at_ argOp)
open VG.X86.Straight (wordAddr)
open VG.Impl.Camellia.X86 (klSlot krSlot kaSlot kbSlot)
open VG.Proof.Camellia (pair byteOf sigE kaW kaD1 kaD2 kaD3)

/-! ## A pair of rounds -/

/-- The halves in the rounds' form, as the value's bytes in `xmm4`. -/
def backOk : Bool :=
  match run params regs₀ backX with
  | none => false
  | some ρ => !(ρ.get .xmm4).sh && (List.range 16).all fun q =>
    (get (ρ.get .xmm4).bs q).same ⟨0, cterms oI (bswq q) (pk (bswq q)), 0#8⟩

theorem back_ok : backOk = true := by lit_decide

/-- The keys of the pairs are those of the constants. -/
theorem sig_all : ((List.range 3).all fun p => (List.range 8).all fun j =>
    byte (tblAt (oSIG p)) (slot j) == dq (sigE (2 * p)) j ^^^ c5 &&
    byte (tblAt (oSIG p)) (slot j + 8) == dq (sigE (2 * p + 1)) j ^^^ c5 ^^^ gc j &&
    byte (tblAt (oSIG p + 16)) (slot j) == dq (sigE (2 * p)) j ^^^ gc j ^^^ c5 &&
    byte (tblAt (oSIG p + 16)) (slot j + 8) == dq (sigE (2 * p + 1)) j ^^^ c5) = true := by
  lit_decide

theorem bswq_rev {j : Nat} (hj : j < 8) : bswq (7 - j) = slot j ∧ bswq (15 - j) = slot j + 8 := by
  unfold bswq slot
  constructor <;> (repeat' split) <;> omega_arith

/-- A register holds the value `v`, its bytes the most significant first. -/
def Val (x : BitVec 128) (v : BitVec 64 × BitVec 64) : Prop :=
  ∀ c < 16, byte x c = byteOf (if c < 8 then v.1 else v.2) (c % 8)

theorem Val.hi {x : BitVec 128} {v : BitVec 64 × BitVec 64} (h : Val x v) {j : Nat} (hj : j < 8) :
    byte x (7 - j) = bz v.1 j := by
  rw [h _ (by omega_arith), ite_eq_left (by omega_arith), bz_byteOf _ hj, show (7 - j) % 8 = 7 - j by omega_arith]

theorem Val.lo {x : BitVec 128} {v : BitVec 64 × BitVec 64} (h : Val x v) {j : Nat} (hj : j < 8) :
    byte x (15 - j) = bz v.2 j := by
  rw [h _ (by omega_arith), ite_eq_right (by omega_arith), bz_byteOf _ hj, show (15 - j) % 8 = 7 - j by omega_arith]

theorem Val.of {x : BitVec 128} {v : BitVec 64 × BitVec 64}
    (h : ∀ j < 8, byte x (7 - j) = bz v.1 j ∧ byte x (15 - j) = bz v.2 j) : Val x v := fun c hc => by
  by_cases h8 : c < 8
  · have := (h (7 - c) (by omega_arith)).1
    rw [show 7 - (7 - c) = c by omega_arith] at this
    rw [this, ite_eq_left h8, bz_byteOf _ (by omega_arith), show 7 - (7 - c) = c % 8 by omega_arith]
  · have := (h (15 - c) (by omega_arith)).2
    rw [show 15 - (15 - c) = c by omega_arith] at this
    rw [this, ite_eq_right h8, bz_byteOf _ (by omega_arith), show 7 - (15 - c) = c % 8 by omega_arith]

theorem Val.xor {x y : BitVec 128} {u v : BitVec 64 × BitVec 64} (hx : Val x u) (hy : Val y v) :
    Val (x ^^^ y) (u.1 ^^^ v.1, u.2 ^^^ v.2) := fun c hc => by
  rw [byte_xor, hx c hc, hy c hc, ← Proof.Camellia.byteOf_xor]
  split <;> rfl

section
variable {s : State}

theorem back_wp (he : Env s) :
    WP isa (.block backX) s fun s' => Same s s' ∧
      ∀ q < 16, byte (s'.xmm .xmm4) q = qI (isA (slot (bswq q % 8))) (pkv s (bswq q)) := by
  have hok := back_ok
  unfold backOk at hok
  split at hok <;> [cases hok; rename_i ρ hrun]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  refine run_wp he.rel hrun fun s' hr hs => ⟨hs, fun q hq => ?_⟩
  rw [same_bytes hr hok.1 hok.2 hq]
  simp only [BV.eval, BitVec.xor_zero, cterms_eval _ (.inr rfl) (bswq_lt hq), env_pk (bswq_lt hq), mask_zero,
    BitVec.zero_xor]
  rfl

/-- The keys of a pair of rounds at `kr`, for the subkeys `ka` and `kb'`. -/
structure PairKeys (s : State) (ka kb' : BitVec 64) : Prop where
  a : ∀ j < 8, kb s (slot j) = dq ka j ^^^ c5
  b : ∀ j < 8, kb s (slot j + 8) = dq kb' j ^^^ c5 ^^^ gc j
  c : ∀ j < 8, kb s (48 + slot j) = dq ka j ^^^ gc j ^^^ c5
  d : ∀ j < 8, kb s (56 + slot j) = dq kb' j ^^^ c5

theorem PairKeys.same {s' : State} {ka kb' : BitVec 64} (h : PairKeys s ka kb') (hs : Same s s') :
    PairKeys s' ka kb' :=
  ⟨fun j hj => by rw [kb_same hs]; exact h.a j hj, fun j hj => by rw [kb_same hs]; exact h.b j hj,
    fun j hj => by rw [kb_same hs]; exact h.c j hj, fun j hj => by rw [kb_same hs]; exact h.d j hj⟩

/-- Two rounds on the value in `xmm0`, to `xmm4`. -/
theorem pairX_wp (htb : s.gpr tbr = s.syms tableName) (hfit : (s.gpr kr).toNat + 128 ≤ 2 ^ 32)
    (hacc : ∀ o, o + 16 ≤ 128 → InRegions (s.rd ++ s.wr) (addr (s.gpr kr) o) 16) {ka kb' : BitVec 64}
    (hk : PairKeys s ka kb') {v : BitVec 64 × BitVec 64} (hv : Val (s.xmm .xmm0) v) :
    WP isa (.block pairX) s fun s' => Same s s' ∧ Val (s'.xmm .xmm4) (pair ka kb' v) := by
  refine WP.block_append_iff.mpr (WP.mono (head_wp htb hfit hacc) fun s₁ ⟨e₁, x₁, m₁⟩ => ?_)
  have k₁ := hk.same e₁
  have he₁ : Env s₁ := by obtain ⟨f, rfl⟩ := e₁; exact ⟨htb, hfit, hacc, m₁⟩
  have h0 : Spread (s₁.xmm .xmm0) fun j => dq v.1 j ^^^ dq ka j ^^^ c5 := fun j hj => by
    rw [(x₁ _ (slot_lt j)).1, slot_slot hj, (bswq_slot hj).1, hk.a j hj, hv.hi hj]
    simp only [dq, BitVec.xor_assoc]
  have h1 : Spread (s₁.xmm .xmm1) fun j => dq v.2 j ^^^ dq kb' j ^^^ c5 ^^^ gc j := fun j hj => by
    rw [(x₁ _ (slot_lt j)).2, slot_slot hj, (bswq_slot hj).2, hk.b j hj, hv.lo hj]
    simp only [dq, BitVec.xor_assoc]
  refine WP.block_append_iff.mpr (WP.mono (lastpair_wp he₁ k₁.c k₁.d h0 h1) fun s₂ ⟨e₂, he₂, x₂, y₂⟩ => ?_)
  refine WP.mono (back_wp he₂) fun s₃ ⟨e₃, x₃⟩ => ⟨(e₁.trans e₂).trans e₃, Val.of fun j hj => ?_⟩
  have sj := slot_lt j
  rw [x₃ _ (by omega_arith), x₃ _ (by omega_arith), (bswq_rev hj).1, (bswq_rev hj).2,
    show slot j % 8 = slot j by omega_arith, show (slot j + 8) % 8 = slot j by omega_arith, slot_slot hj, pkv, pkv,
    ite_eq_left sj, ite_eq_right (by omega_arith), Nat.add_sub_cancel, x₂ j hj, y₂ j hj]
  exact ⟨qI_qT _ _, qI_qT _ _⟩

end

/-! ## `KA` and `KB` -/

/-- The four words at slot `a` hold a value if the 16 bytes there do. -/
theorem VW_iff {s : State} {b : BitVec 32} (hb : s.gpr sb = b) {a : Nat} (hfit : b.toNat + 4 * a + 16 ≤ 2 ^ 32)
    {v : BitVec 64 × BitVec 64} : VW s a v ↔ Val (s.mem.readW (addr b (4 * a)) 128) v := by
  have key : ∀ c < 16, ∀ j < 8, (slotW s (a + c / 4)).getLsbD (8 * (c % 4) + j) =
      (byte (s.mem.readW (addr b (4 * a)) 128) c).getLsbD j := fun c hc j hj => by
    have e1 : ∀ i, ((slotW s (a + c / 4)).extractLsb' (8 * (c % 4)) 8).getLsbD i =
        (byte (s.mem.readW (addr b (4 * a)) 128) c).getLsbD i := fun i => by
      show ((s.mem.readW (addr (s.gpr sb) (4 * (a + c / 4))) 32).extractLsb' (8 * (c % 4)) 8).getLsbD i =
        ((s.mem.readW (addr b (4 * a)) 128).extractLsb' (8 * c) 8).getLsbD i
      rw [hb, byte_readW _ _ (by omega_arith), byte_readW _ _ (by omega_arith), addr_eq (by omega_arith),
        addr_eq (by omega_arith), Offset.add_ofNat_add_ofNat, Offset.add_ofNat_add_ofNat,
        show 4 * (a + c / 4) + c % 4 = 4 * a + c by omega_arith]
    rw [← e1 j, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
  constructor
  · intro h c hc
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    rw [← key c hc j hj]; exact h c hc j hj
  · intro h c hc j hj
    rw [key c hc j hj, h c hc]

section
variable {s : State} {is : List Instr} {Q : State → Prop}

/-- A 16-byte load. -/
theorem wp_ldx {d : XReg} {r : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr r = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 16)
    (k : WP isa (.block is) (s.setXmm d (s.mem.readW (addr B o) 128)) Q) :
    WP isa (.block (ld d r o :: is)) s Q := by
  refine Wp.cons ?_ k
  show (s.load128 (addr (s.gpr r) o)).map _ = _
  rw [hb, State.load128, ite_eq_left hin]; rfl

/-- A 16-byte store. -/
theorem wp_stx {d : XReg} {r : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr r = B)
    (hin : InRegions s.wr (addr B o) 16)
    (k : WP isa (.block is) { s with mem := s.mem.writeW (addr B o) (s.xmm d) } Q) :
    WP isa (.block (stx r o d :: is)) s Q := by
  refine Wp.cons ?_ k
  show s.store128 (addr (s.gpr r) o) _ = _
  rw [hb, State.store128, ite_eq_left hin]

theorem wp_pxor {a c : XReg} (k : WP isa (.block is) (s.setXmm a (s.xmm a ^^^ s.xmm c)) Q) :
    WP isa (.block (x .pxor a c :: is)) s Q := Wp.cons rfl k

/-- A load of the table. -/
theorem wp_tb {d : XReg} {o : Nat} (htb : s.gpr tbr = s.syms tableName) (ho : o % 8 = 0 ∧ o / 8 + 2 ≤ table.length)
    (k : WP isa (.block is) (s.setXmm d (tblAt o)) Q) : WP isa (.block (tb d o :: is)) s Q := by
  refine Wp.cons ?_ k
  show (if s.gpr tbr = s.syms tableName ∧ o % 8 = 0 ∧ o / 8 + 2 ≤ table.length then _ else none) = _
  rw [ite_eq_left ⟨htb, ho⟩]; rfl

end

/-- The keys of the pairs before `n` are in the scratch buffer. -/
def KeysTo (m : Mem) (b : BitVec 32) (n : Nat) : Prop := ∀ p < n,
  m.readW (addr b (32 * p)) 128 = tblAt (oSIG p) ∧ m.readW (addr b (32 * p + 48)) 128 = tblAt (oSIG p + 16)

theorem sep16 {b : BitVec 32} {o o' : Nat} (h1 : b.toNat + o + 16 ≤ 2 ^ 32) (h2 : b.toNat + o' + 16 ≤ 2 ^ 32)
    (h : o + 16 ≤ o' ∨ o' + 16 ≤ o) : Mem.Sep (addr b o) (128 / 8) (addr b o') (128 / 8) := by
  rw [addr_eq (by omega_arith), addr_eq (by omega_arith)]
  exact Offset.sep _ h (by omega_arith) (by omega_arith)

/-- What the code for `KA` and `KB` keeps, with `kr` at the keys of pair `p`. -/
structure At (s₀ : State) (b : BitVec 32) (p : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  kp : s.gpr kr = b + BitVec.ofNat 32 (32 * p)
  tb : s.gpr tbr = s.syms tableName
  gpr : ∀ r, r ≠ kr → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keys : KeysTo s.mem b 3
  frame : Frame [⟨b.setWidth 64 + BitVec.ofNat 64 336, 32⟩] s₀.mem s.mem

section
variable {s₀ s : State} {b : BitVec 32} {p : Nat}

theorem At.xmm (h : At s₀ b p s) (f : XReg → BitVec 128) : At s₀ b p { s with xmm := f } :=
  ⟨h.base, h.kp, h.tb, h.gpr, h.rd, h.wr, h.keys, h.frame⟩

theorem At.same {s' : State} (h : At s₀ b p s) (hs : Same s s') : At s₀ b p s' := by
  obtain ⟨f, rfl⟩ := hs
  exact h.xmm f

theorem KeysTo.store {m : Mem} {n o : Nat} (h : KeysTo m b n) (hfit : b.toNat + 384 ≤ 2 ^ 32) (hn : n ≤ 3)
    (ho : o + 16 ≤ 384) (hk : ∀ q < n, (o + 16 ≤ 32 * q ∨ 32 * q + 16 ≤ o) ∧ (o + 16 ≤ 32 * q + 48 ∨ 32 * q + 64 ≤ o))
    (v : BitVec 128) : KeysTo (m.writeW (addr b o) v) b n := fun q hq => by
  have := hk q hq
  rw [Mem.readW_writeW_sep (sep16 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
    Mem.readW_writeW_sep (sep16 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
  exact h q hq

/-- The keys of pair `p`, to the scratch buffer. -/
theorem keysOne_wp {is : List Instr} {Q : State → Prop} (hp : p < 3) (hb : s.gpr sb = b)
    (htb : s.gpr tbr = s.syms tableName) (hw : ScrInN 96 s.wr b) (hk : KeysTo s.mem b p)
    (k : ∀ s' : State, s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.syms = s.syms → KeysTo s'.mem b (p + 1) →
      Frame [⟨b.setWidth 64, 192⟩] s.mem s'.mem → WP isa (.block is) s' Q) :
    WP isa (.block (keysOne p ++ is)) s Q := by
  have hfit := hw.fit
  have hin : ∀ o, o + 16 ≤ 384 → InRegions s.wr (addr b o) 16 := fun o ho => by
    obtain ⟨n, hn, hf, hr⟩ := hw.mem
    exact ⟨_, hr, by rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have htl : table.length = 76 := by decide
  show WP isa (.block (tb .xmm0 (oSIG p) :: stx sb (32 * p) .xmm0 :: tb .xmm0 (oSIG p + 16) ::
    stx sb (32 * p + 48) .xmm0 :: is)) s Q
  refine wp_tb htb (by rw [htl, oSIG]; omega_arith) ?_
  refine wp_stx (B := b) hb (hin _ (by omega_arith)) ?_
  refine wp_tb htb (by rw [htl, oSIG]; omega_arith) ?_
  refine wp_stx (B := b) hb (hin _ (by omega_arith)) ?_
  refine k _ rfl rfl rfl rfl ?_ ?_
  · intro q hq
    by_cases h : q < p
    · exact ((hk.store (by omega_arith) (by omega_arith) (o := 32 * p) (by omega_arith) (fun q hq => by omega_arith) _).store
        (by omega_arith) (by omega_arith) (o := 32 * p + 48) (by omega_arith) (fun q hq => by omega_arith) _) q h
    · obtain rfl : q = p := by omega_arith
      refine ⟨?_, Mem.readW_writeW_self _ _ 16 _ (by decide)⟩
      exact (Mem.readW_writeW_sep (sep16 (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)).trans
        (Mem.readW_writeW_self _ _ 16 _ (by decide))
  · have c : ∀ o, o + 16 ≤ 192 → Region.Contains ⟨b.setWidth 64, 192⟩ (addr b o) 16 := fun o ho => by
      rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c _ (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (c _ (by omega_arith))

theorem At.adr (h : At s₀ b p s) (hf : b.toNat + 384 ≤ 2 ^ 32) (hp : p < 3) {o : Nat} (ho : o ≤ 128) :
    addr (s.gpr kr) o = b.setWidth 64 + BitVec.ofNat 64 (32 * p + o) := by
  rw [h.kp, show addr (b + BitVec.ofNat 32 (32 * p)) o = addr b (32 * p + o) by
    rw [addr, addr, Offset.add_ofNat_add_ofNat], addr_eq (by omega_arith)]

theorem At.keyByte (h : At s₀ b p s) (hf : b.toNat + 384 ≤ 2 ^ 32) (hp : p < 3) {q : Nat} (hq : q < 16) :
    kb s q = byte (tblAt (oSIG p)) q ∧ kb s (48 + q) = byte (tblAt (oSIG p + 16)) q := by
  obtain ⟨e1, e2⟩ := h.keys p hp
  have kr64 : (s.gpr kr).setWidth 64 = b.setWidth 64 + BitVec.ofNat 64 (32 * p) := by
    rw [h.kp]; exact addr_eq (by omega_arith)
  have rd : ∀ o, o + 16 ≤ 384 → byte (s.mem.readW (addr b o) 128) q = s.mem (b.setWidth 64 + BitVec.ofNat 64 (o + q)) :=
    fun o ho => by
      rw [byte, byte_readW _ _ (by omega_arith), addr_eq (by omega_arith), Offset.add_ofNat_add_ofNat]
  refine ⟨?_, ?_⟩
  · rw [← e1, rd _ (by omega_arith), kb, kr64, Offset.add_ofNat_add_ofNat]
  · rw [← e2, rd _ (by omega_arith), kb, kr64, Offset.add_ofNat_add_ofNat,
      show 32 * p + (48 + q) = 32 * p + 48 + q by omega_arith]

theorem At.pairKeys (h : At s₀ b p s) (hf : b.toNat + 384 ≤ 2 ^ 32) (hp : p < 3) :
    PairKeys s (sigE (2 * p)) (sigE (2 * p + 1)) := by
  have hs := fun j (hj : j < 8) => List.all_eq_true.mp (List.all_eq_true.mp sig_all p (List.mem_range.mpr hp)) j
    (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  have sl := slot_lt
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [(h.keyByte hf hp (by have := sl j; omega_arith)).1]; exact (hs j hj).1.1.1
  · rw [(h.keyByte hf hp (by have := sl j; omega_arith)).1]; exact (hs j hj).1.1.2
  · rw [(h.keyByte hf hp (by have := sl j; omega_arith)).2]; exact (hs j hj).1.2
  · rw [show 56 + slot j = 48 + (slot j + 8) by omega_arith, (h.keyByte hf hp (by have := sl j; omega_arith)).2]
    exact (hs j hj).2

/-- A pair of rounds, in place. -/
theorem At.pair_wp {is : List Instr} {Q : State → Prop} (h : At s₀ b p s) (hw : ScrInN 96 s₀.wr b) (hp : p < 3)
    {v : BitVec 64 × BitVec 64} (hv : Val (s.xmm .xmm0) v)
    (k : ∀ s', At s₀ b p s' → s'.mem = s.mem → Val (s'.xmm .xmm4) (pair (sigE (2 * p)) (sigE (2 * p + 1)) v) →
      WP isa (.block is) s' Q) : WP isa (.block (pairX ++ is)) s Q := by
  have hf := hw.fit
  have krN : (s.gpr kr).toNat = b.toNat + 32 * p := by
    rw [h.kp, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (a := 32 * p) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  refine WP.block_append_iff.mpr (WP.mono (pairX_wp h.tb (by omega_arith) (fun o ho => ?_) (h.pairKeys hf hp) hv)
    fun s' ⟨e, v'⟩ => k s' (h.same e) ?_ v')
  · obtain ⟨n, hn, hf', hr⟩ := hw.mem
    refine ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hr), ?_⟩
    rw [h.adr hf hp (by omega_arith)]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · obtain ⟨f, rfl⟩ := e; rfl

/-- On to the next pair's keys. -/
theorem At.next_wp {is : List Instr} {Q : State → Prop} (h : At s₀ b p s)
    (k : ∀ s', At s₀ b (p + 1) s' → s'.mem = s.mem → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (nextKeys :: is)) s Q := by
  refine wp_addi_x fun s' u xe => k s' ⟨?_, ?_, ?_, fun r hr => ?_, u.rd.trans h.rd, u.wr.trans h.wr,
    by rw [u.mem]; exact h.keys, by rw [u.mem]; exact h.frame⟩ u.mem xe
  · rw [u.other _ (by decide)]; exact h.base
  · rw [u.gpr, h.kp, show (32 : BitVec 32) = BitVec.ofNat 32 32 from rfl, Offset.add_ofNat_add_ofNat,
      show 32 * p + 32 = 32 * (p + 1) by omega_arith]
  · rw [u.other _ (by decide), u.syms]; exact h.tb
  · rw [u.other r hr]; exact h.gpr r hr

/-- A value of the scratch buffer, to a register. -/
theorem At.ld_wp {is : List Instr} {Q : State → Prop} {d : XReg} {a : Nat} (h : At s₀ b p s)
    (hw : ScrInN 96 s₀.wr b) (ha : a + 4 ≤ 96)
    (k : ∀ s', At s₀ b p s' → s'.mem = s.mem → s'.xmm d = s.mem.readW (addr b (4 * a)) 128 →
      (∀ r, r ≠ d → s'.xmm r = s.xmm r) → WP isa (.block is) s' Q) :
    WP isa (.block (ldV d a :: is)) s Q := by
  have hf := hw.fit
  obtain ⟨n, hn, hf', hr⟩ := hw.mem
  exact wp_ldx h.base ⟨_, List.mem_append_right _ (by rw [h.wr]; exact hr), by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    (k _ (h.xmm _) rfl (ite_eq_left rfl) fun r hr => ite_eq_right hr)

theorem At.pxor_wp {is : List Instr} {Q : State → Prop} {d c : XReg} (h : At s₀ b p s)
    (k : ∀ s', At s₀ b p s' → s'.mem = s.mem → s'.xmm d = s.xmm d ^^^ s.xmm c → WP isa (.block is) s' Q) :
    WP isa (.block (x .pxor d c :: is)) s Q :=
  wp_pxor (k _ (h.xmm _) rfl (ite_eq_left rfl))

/-- `KA` or `KB`, to the scratch buffer. -/
theorem At.st_wp {is : List Instr} {Q : State → Prop} {a : Nat} (h : At s₀ b p s)
    (hw : ScrInN 96 s₀.wr b) (ha1 : 84 ≤ a) (ha2 : a + 4 ≤ 92)
    (k : ∀ s', At s₀ b p s' → s'.xmm = s.xmm → s'.mem = s.mem.writeW (addr b (4 * a)) (s.xmm .xmm4) →
      WP isa (.block is) s' Q) : WP isa (.block (stx sb (4 * a) .xmm4 :: is)) s Q := by
  have hf := hw.fit
  obtain ⟨n, hn, hf', hr⟩ := hw.mem
  have hc : Region.Contains ⟨b.setWidth 64 + BitVec.ofNat 64 336, 32⟩ (addr b (4 * a)) 16 := by
    rw [addr_eq (by omega_arith)]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine wp_stx h.base ⟨_, by rw [h.wr]; exact hr, by
    rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    (k _ ⟨h.base, h.kp, h.tb, h.gpr, h.rd, h.wr, h.keys.store (by omega_arith) (by decide) (by omega_arith)
      (fun q hq => by omega_arith) _, h.frame.writeW (List.mem_singleton_self _) _ hc⟩ rfl rfl)

/-- `KL` and `KR` stay. -/
theorem At.val (h : At s₀ b p s) (hf : b.toNat + 384 ≤ 2 ^ 32) {a : Nat} (ha : a + 4 ≤ 84) :
    s.mem.readW (addr b (4 * a)) 128 = s₀.mem.readW (addr b (4 * a)) 128 := by
  rw [addr_eq (by omega_arith)]
  exact h.frame.readW (r := ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * a), 16⟩) (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)

theorem kaKb_wp (h : At s₀ b 0 s₀) (hw : ScrInN 96 s₀.wr b) {KL KR : BitVec 64 × BitVec 64}
    (hl : VW s₀ klSlot KL) (hr : VW s₀ krSlot KR) :
    WP isa (.block kaKb) s₀ fun s => At s₀ b 2 s ∧ VW s kaSlot (kaD2 KL KR) ∧ VW s kbSlot (kaD3 KL KR) := by
  have hf := hw.fit
  have VL := (VW_iff h.base (a := klSlot) (by rw [klSlot_eq]; omega_arith)).mp hl
  have VR := (VW_iff h.base (a := krSlot) (by rw [krSlot_eq]; omega_arith)).mp hr
  unfold kaKb
  -- `KL ^ KR`, and its pair.
  refine h.ld_wp hw (by decide) fun u₁ b₁ n₁ e₁ _ => ?_
  refine b₁.ld_wp hw (by decide) fun u₂ b₂ n₂ e₂ o₂ => ?_
  refine b₂.pxor_wp fun u₃ b₃ n₃ e₃ => ?_
  refine b₃.pair_wp hw (by decide) (v := kaW KL KR 0) ?_ fun s₁ a₁ m₁ v₁ => ?_
  · rw [e₃, e₂, o₂ _ (by decide), e₁, n₁]; exact VL.xor VR
  -- `KL` again.
  refine a₁.ld_wp hw (by decide) fun u₄ b₄ n₄ e₄ o₄ => ?_
  refine b₄.pxor_wp fun u₅ b₅ n₅ e₅ => ?_
  refine b₅.next_wp fun u₆ b₆ n₆ x₆ => ?_
  refine b₆.pair_wp hw (by decide) (v := kaW KL KR 1) ?_ fun s₂ a₂ m₂ v₂ => ?_
  · have := VL.xor v₁
    rw [x₆, e₅, e₄, o₄ _ (by decide), a₁.val hf (by decide)]
    simp only [kaW, BitVec.xor_comm _ KL.1, BitVec.xor_comm _ KL.2]
    exact this
  -- `KA`, and `KR`.
  refine a₂.st_wp hw (by decide) (by decide) fun s₃ a₃ x₃ m₃ => ?_
  refine a₃.ld_wp hw (by decide) fun u₇ b₇ n₇ e₇ o₇ => ?_
  refine b₇.pxor_wp fun u₈ b₈ n₈ e₈ => ?_
  refine b₈.next_wp fun u₉ b₉ n₉ x₉ => ?_
  refine b₉.pair_wp hw (by decide) (v := kaW KL KR 2) ?_ fun s₄ a₄ m₄ v₄ => ?_
  · have := VR.xor v₂
    rw [x₉, e₈, e₇, o₇ _ (by decide), a₃.val hf (by decide), x₃]
    simp only [kaW, BitVec.xor_comm _ KR.1, BitVec.xor_comm _ KR.2]
    exact this
  -- `KB`.
  refine a₄.st_wp hw (by decide) (by decide) fun s₅ a₅ x₅ m₅ => WP.block_nil ⟨a₅, ?_, ?_⟩
  · refine (VW_iff a₅.base (a := kaSlot) (by show b.toNat + 4 * 84 + 16 ≤ _; omega_arith)).mpr ?_
    have sp : Mem.Sep (addr b (4 * kaSlot)) (128 / 8) (addr b (4 * kbSlot)) (128 / 8) :=
      sep16 (by show b.toNat + 336 + 16 ≤ _; omega_arith) (by show b.toNat + 352 + 16 ≤ _; omega_arith) (.inl (by decide))
    rw [m₅, Mem.readW_writeW_sep sp (by decide), m₄, n₉, n₈, n₇, m₃]
    exact (congrArg (Val · _) (Mem.readW_writeW_self _ _ 16 _ (by decide))).mpr v₂
  · refine (VW_iff a₅.base (a := kbSlot) (by show b.toNat + 4 * 88 + 16 ≤ _; omega_arith)).mpr ?_
    rw [m₅]
    exact (congrArg (Val · _) (Mem.readW_writeW_self _ _ 16 _ (by decide))).mpr v₄

end

/-! ## The whole function -/

section
variable {s₀ : State} {b : BitVec 32}

/-- A slot outside a frame. -/
theorem slot_fr {m m' : Mem} {rs : List Region} (f : Frame rs m m') (hf : b.toNat + 384 ≤ 2 ^ 32) {k : Nat}
    (hk : k < 96) (hd : ∀ r ∈ rs, Region.Disjoint ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * k), 4⟩ r) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [wordAddr, addr_eq (by omega_arith)]
  exact f.readW (Region.contains_self _ _) hd (by decide)

/-- The keys' area is apart from the slots after it. -/
theorem keys_disj {k : Nat} (h : 48 ≤ k) (hk : k < 96) :
    ∀ r ∈ [(⟨b.setWidth 64, 192⟩ : Region)], Region.Disjoint ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * k), 4⟩ r :=
  fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

/-- `KA`'s and `KB`'s slots are apart from the others. -/
theorem kaKb_disj {k : Nat} (h : k < 84 ∨ 92 ≤ k) (hk : k < 96) :
    ∀ r ∈ [(⟨b.setWidth 64 + BitVec.ofNat 64 336, 32⟩ : Region)],
      Region.Disjoint ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * k), 4⟩ r := fun r hr => by
  rw [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The keys' copy, then `KA` and `KB`. -/
theorem rounds_wp {s : State} (hb : s.gpr sb = b) (ht : s.gpr .edx = s.syms tableName) (hw : ScrInN 96 s.wr b)
    {KL KR : BitVec 64 × BitVec 64} (hl : VW s klSlot KL) (hr : VW s krSlot KR) :
    WP isa (.block mid) s fun s' =>
      s'.gpr sb = b ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VW s' klSlot KL ∧ VW s' krSlot KR ∧ VW s' kaSlot (kaD2 KL KR) ∧ VW s' kbSlot (kaD3 KL KR) ∧
      (∀ k, 92 ≤ k → k < 96 → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      Frame [⟨b.setWidth 64, 4 * 96⟩] s.mem s'.mem := by
  have hf := hw.fit
  show WP isa (.block (.mov tbr (.reg .edx) :: .mov kr (.reg sb) :: (keysIn ++ kaKb))) s _
  rw [show keysIn ++ kaKb = keysOne 0 ++ (keysOne 1 ++ (keysOne 2 ++ kaKb)) by simp only [keysIn, List.append_assoc]]
  refine Wp.wp_mov fun s₁ u₁ => ?_
  refine Wp.wp_mov fun s₂ u₂ => ?_
  have b₂ : s₂.gpr sb = b := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb]
  have t₂ : s₂.gpr tbr = s₂.syms tableName := by
    rw [u₂.other _ (by decide), u₁.gpr, u₂.syms, u₁.syms, ht]
  have k₂ : s₂.gpr kr = b := by rw [u₂.gpr, u₁.other _ (by decide), hb]
  have w₂ : ScrInN 96 s₂.wr b := by rw [u₂.wr, u₁.wr]; exact hw
  have m₂ : s₂.mem = s.mem := u₂.mem.trans u₁.mem
  refine keysOne_wp (p := 0) (by decide) b₂ t₂ w₂ (fun q h => absurd h (Nat.not_lt_zero _)) fun s₃ g₃ r₃ wr₃ y₃ K₃ f₃ => ?_
  refine keysOne_wp (p := 1) (by decide) (by rw [g₃, b₂]) (by rw [g₃, y₃]; exact t₂) (by rw [wr₃]; exact w₂) K₃
    fun s₄ g₄ r₄ wr₄ y₄ K₄ f₄ => ?_
  refine keysOne_wp (p := 2) (by decide) (by rw [g₄, g₃, b₂]) (by rw [g₄, y₄, g₃, y₃]; exact t₂)
    (by rw [wr₄, wr₃]; exact w₂) K₄ fun s₅ g₅ r₅ wr₅ y₅ K₅ f₅ => ?_
  have g : s₅.gpr = s₂.gpr := g₅.trans (g₄.trans g₃)
  have f : Frame [⟨b.setWidth 64, 192⟩] s.mem s₅.mem := by rw [← m₂]; exact (f₃.trans f₄).trans f₅
  have keep : ∀ k, 48 ≤ k → k < 96 → s₅.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 :=
    fun k h1 h2 => slot_fr f (by omega_arith) h2 (keys_disj h1 h2)
  have vw : ∀ a v, 48 ≤ a → a + 4 ≤ 96 → VW s a v → VW s₅ a v := fun a v h1 h2 h => h.congr fun i hi => by
    show s₅.mem.readW (wordAddr (s₅.gpr sb) (a + i)) 32 = s.mem.readW (wordAddr (s.gpr sb) (a + i)) 32
    rw [g, b₂, hb]; exact keep _ (by omega_arith) (by omega_arith)
  have at₅ : At s₅ b 0 s₅ := ⟨by rw [g, b₂], by rw [g, k₂]; simp, by rw [g, y₅, y₄, y₃]; exact t₂, fun _ _ => rfl, rfl, rfl,
    K₅, Frame.refl _ _⟩
  refine WP.mono (kaKb_wp at₅ (by rw [wr₅, wr₄, wr₃]; exact w₂) (vw _ _ (by decide) (by decide) hl)
    (vw _ _ (by decide) (by decide) hr)) fun s₆ ⟨a₆, ka, kb'⟩ => ?_
  have keep₆ : ∀ k, (k < 84 ∨ 92 ≤ k) → k < 96 → s₆.mem.readW (wordAddr b k) 32 = s₅.mem.readW (wordAddr b k) 32 :=
    fun k h1 h2 => slot_fr a₆.frame (by omega_arith) h2 (kaKb_disj h1 h2)
  have vw₆ : ∀ a v, a + 4 ≤ 84 → VW s₅ a v → VW s₆ a v := fun a v h1 h => h.congr fun i hi => by
    show s₆.mem.readW (wordAddr (s₆.gpr sb) (a + i)) 32 = s₅.mem.readW (wordAddr (s₅.gpr sb) (a + i)) 32
    rw [a₆.base, at₅.base]; exact keep₆ _ (.inl (by omega_arith)) (by omega_arith)
  refine ⟨a₆.base, ?_, by rw [a₆.rd, r₅, r₄, r₃, u₂.rd, u₁.rd], by rw [a₆.wr, wr₅, wr₄, wr₃, u₂.wr, u₁.wr],
    vw₆ _ _ (by decide) (vw _ _ (by decide) (by decide) hl), vw₆ _ _ (by decide) (vw _ _ (by decide) (by decide) hr),
    ka, kb', fun k h1 h2 => ?_, ?_⟩
  · rw [a₆.gpr _ (by decide), g, u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [keep₆ k (.inr h1) h2, keep k (by omega_arith) h2]
  · refine (f.sub fun r hr => ?_).trans (a₆.frame.sub fun r hr => ?_) <;> rw [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩

end

/-! ## The contract, and constant time -/

theorem mid_ok : MidOk 96 tableName mid := fun hb ht hw hl hr => rounds_wp hb ht hw hl hr

theorem expandKey_ct : ConstantTime isa (expandKeyC 96).pre (expandKeyC 96).pub expandKey :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) (ekTaint 96) (fun _ _ h₁ h₂ hp => ekTaint_agree h₁ h₂ hp) (by taint_decide)

/-- Memory holding the arguments `0x1000, 16, 0x2000, 0x3000` at `0x8004`. -/
def sat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800D then 0x20 else
    if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 16⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x2000, 272⟩, ⟨0x3000, 384⟩]

theorem expandKey_verified :
    Verified X86.target expandKey (Proof.Camellia.expandKeyScratchContract X86.abi 48 4) :=
  Verified.of_correct (fun _ hs => expandKey_wp (by decide) mid_ok hs) expandKey_ct (by
    sig_implies [Proof.Camellia.expandKeyScratchContract, Proof.Camellia.expandKeyScratchSig,
      Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre, Spec.Camellia.expandKeyPost, expandKeyC, expandKeyX86N,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [sat, arg, argAddr, Mem.readW, Mem.read] using sat)

/-- A state satisfying `vg_camellia_expand_key`'s precondition: a key of 16
bytes at `0x1000` and the schedule at `0x2000`, as stack arguments at
`0x8004`. -/
theorem frameSat : ∃ s, (Spec.Camellia.expandKeyContract X86.abi 420).pre s := by
  implies_sat [Spec.Camellia.expandKeyContract, Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre,
    Spec.Camellia.expandKeyPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [expandKeyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using expandKeyFrameSat

/-- `expandKey` with its working space on the stack. -/
theorem expandKey_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 416 3 96 expandKey)
      (Spec.Camellia.expandKeyContract X86.abi 420) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.expandKeySig) (nm := "scratch") (e := .u64) (n := 48)
    (pre := Spec.Camellia.expandKeyPre X86.abi.ptrBits) (post := Spec.Camellia.expandKeyPost X86.abi.ptrBits)
    (wa := false) (stack := 4) (bytes := 416)
    (by rw [← Proof.Camellia.expandKeyScratchContract_eq]; exact expandKey_verified)
    (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.expandKeyPre_local _) (Proof.Camellia.expandKeyPost_local _)
    (Proof.Camellia.expandKeyPostOut_local _) frameSat

/-- `Spec.Camellia.expandKeyApi` as emitted (`Impl.Camellia.X86.AesNiKey.Fn.expandKey`) meets its contract
in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.AesNiKey.Fn.expandKey (Spec.Camellia.expandKeyContract X86.abi 420) 0 :=
  X86.Scrub.verifiedScrubbedSel (api := Spec.Camellia.expandKeyApi) (W := 420)
    { code := Impl.StackScratch.X86.withStackScratchWiped 416 3 96 expandKey
      verified := expandKey_framed }
    Fn.words (X86.Scrub.postOut_of_local (leak := none) X86.Scrub.ScrubAbi.plain
      (Proof.Camellia.expandKeyPostOut_local _)) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Camellia.X86.AesNiKey
