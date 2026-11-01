module

public import VerifiedGarbage.Proof.Aes.RISCV64.Chain
public import VerifiedGarbage.Proof.Aes.RISCV64.ChainFrame
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Chain
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Aes.RISCV64.Blocks
meta import VerifiedGarbage.Proof.Aes.RISCV64.Chain
meta import VerifiedGarbage.Proof.Aes.RISCV64.ChainFrame
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Chain
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
meta import VerifiedGarbage.Proof.AesCfb.Spec
meta import VerifiedGarbage.Proof.AesOfb.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.Aes.RISCV64.Blocks
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES-CFB128 encryption and AES-OFB on RISC-V: the chains

`cfbChain` and `ofbChain` (`Impl/Aes/RISCV64/Chain.lean`) run `chain`'s
frame (`ChainFrame.lean`) with a loop that enciphers the state in the
registers of block 0 (`enc_ok`), then, for CFB128, XORs the data block into
it and stores it over the block (`Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, the state), or, for
OFB, stores the data block XORed with it (`Oⱼ = CIPH_K(Oⱼ₋₁)`, the state).
After `k` blocks (`MAt`) the state is `st k` and the first `k` blocks are
`F`'s (`EcbInv`): for CFB128 `cfbSt`, its blocks the states after them, for
OFB `ofbSt`, its blocks XORed with the states after them. Their contract
(`blockKRISCV64 M`) is the modes' (`AesCbc.RISCV64.modeRISCV64`), with the
first 2048 bytes of the scratch buffer, as the chain's (`modeK_correct`,
for any such loop). They are constant time by taint tracking, and
`cfbChain_k`, `ofbChain_k` state them as chains to call
(`AesCbc.RISCV64.ChainK`).
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.RISCV64 in
/-- RISC-V contract for a chaining function of the mode `M` on whole blocks
(`Impl.Aes.RISCV64.cfbChain`, `ofbChain`), with the arguments
`(schedule = a0, rounds = a1, iv = a2, data = a3, n = a4, scratch = a5)`:
`modeRISCV64 M`'s postcondition, with `chainRISCV64 true`'s precondition (a
scratch buffer of 2048 bytes). -/
def blockKRISCV64 (M : AesCbc.Mode) : Contract RISCV64.isa where
  pre := RISCV64.framePre true (16 * ·)
  post := (AesCbc.RISCV64.modeRISCV64 M).post
  pub := (chainRISCV64 true).pub

end VG.Proof.Aes

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes

/-! ## The states -/

/-- CFB128's chaining values: `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`. -/
def cfbSt (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) : Nat → Spec.Aes.State
  | 0 => iv
  | k + 1 => vxor (Spec.Aes.cipher R w (cfbSt R w m₀ D iv k)) (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * k)))

/-- CFB128's blocks: the chaining values after them. -/
abbrev cfbF (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) (j : Nat) : Spec.Aes.State :=
  cfbSt R w m₀ D iv (j + 1)

/-- OFB's output blocks: `Oⱼ = CIPH_K(Oⱼ₋₁)`. -/
def ofbSt (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) : Nat → Spec.Aes.State
  | 0 => iv
  | k + 1 => Spec.Aes.cipher R w (ofbSt R w m₀ D iv k)

/-- OFB's blocks: XORed with the output blocks. -/
abbrev ofbF (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) (j : Nat) : Spec.Aes.State :=
  vxor (ofbSt R w m₀ D iv (j + 1)) (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * j)))

theorem aesWith_toList (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    Spec.Cbc.aesWith R w x.toList = (Spec.Aes.cipher R w x).toList := by
  rw [Spec.Cbc.aesWith, ofFn_toList]

/-- The last of the blocks `g 1 … g k` after `g 0`. -/
theorem next_range (g : Nat → List Byte) : ∀ k, Spec.Cbc.next (g 0) ((List.range k).map fun j => g (j + 1)) = g k
  | 0 => rfl
  | k + 1 => by
    simp only [Spec.Cbc.next, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    exact List.getLastD_concat

theorem take_blocksAt (m : Mem) (D : Addr) {n k : Nat} (hk : k < n) :
    (Spec.Cbc.blocksAt m D n).take (k + 1) =
      (Spec.Cbc.blocksAt m D n).take k ++ [Spec.Aes.bytesAt m (D + BitVec.ofNat 64 (16 * k)) 16] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cbc.blocksAt]; omega)]
  simp [Spec.Cbc.blocksAt]

/-- CFB128 encryption of the first `k` blocks: block `j` the chaining value after it. -/
theorem cfb_encrypt_eq (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) {n : Nat} :
    ∀ k ≤ n, Spec.Cfb.encrypt (Spec.Cbc.aesWith R w) iv.toList ((Spec.Cbc.blocksAt m₀ D n).take k) =
      (List.range k).map fun j => (cfbSt R w m₀ D iv (j + 1)).toList
  | 0, _ => by simp [Spec.Cfb.encrypt]
  | k + 1, hk => by
    have hn := next_range (fun j => (cfbSt R w m₀ D iv j).toList) k
    rw [show cfbSt R w m₀ D iv 0 = iv from rfl] at hn
    rw [take_blocksAt _ _ (by omega), AesCfb.encrypt_snoc, cfb_encrypt_eq R w m₀ D iv k (by omega),
      hn, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, AesCbc.bytesAt_toList, aesWith_toList, cbcXor_comm, ← toList_vxor]
    rfl

/-- OFB's block to continue from after `k` blocks. -/
theorem ofb_next_eq (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) :
    ∀ k, Spec.Ofb.next (Spec.Cbc.aesWith R w) iv.toList k = (ofbSt R w m₀ D iv k).toList
  | 0 => rfl
  | k + 1 => by rw [AesOfb.next_succ, ofb_next_eq R w m₀ D iv k, aesWith_toList]; rfl

/-- OFB of the first `k` blocks: block `j` XORed with the output block after it. -/
theorem ofb_crypt_eq (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) {n : Nat} :
    ∀ k ≤ n, Spec.Ofb.crypt (Spec.Cbc.aesWith R w) iv.toList ((Spec.Cbc.blocksAt m₀ D n).take k) =
      (List.range k).map fun j => (ofbF R w m₀ D iv j).toList
  | 0, _ => by simp [Spec.Ofb.crypt, Spec.Ofb.outputs]
  | k + 1, hk => by
    rw [take_blocksAt _ _ (by omega), AesOfb.crypt_snoc, ofb_crypt_eq R w m₀ D iv k (by omega),
      List.length_take, Spec.Cbc.blocksAt, List.length_map, List.length_range,
      Nat.min_eq_left (by omega), ofb_next_eq R w m₀ D iv k, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, AesCbc.bytesAt_toList, aesWith_toList, cbcXor_comm, ← toList_vxor]
    rfl

/-! ## The loop -/

/-- After `k` blocks: the state `st k` in the registers of block 0, the
first `k` blocks `F`'s. -/
structure MAt (m₀ : Mem) (s₂ : State) (b D : Addr) (n : Nat) (st F : Nat → Spec.Aes.State) (k : Nat)
    (s : State) : Prop where
  hk : k ≤ n
  a3 : s.gpr .a3 = D + BitVec.ofNat 64 (16 * k)
  a4 : s.gpr .a4 = BitVec.ofNat 64 (n - k)
  keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (eRegions b D n) s₂.mem s.mem
  st : regBlock (Q s) 0 = st k
  data : EcbInv m₀ s.mem D n k F

section Loop

variable {m₀ : Mem} {s₂ : State} {X b D : Addr} {n R : Nat} {w : List Byte}
  {st F : Nat → Spec.Aes.State}

/-- The state enciphered in the registers of block 0. -/
theorem enc_ok (hs : ChSetup true s₂ X b D n R w) {s : State}
    (keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s.gpr r = s₂.gpr r)
    (hwr : s.wr = s₂.wr) (hf : Frame (eRegions b D n) s₂.mem s.mem) :
    WP isa encrypt4 s fun s₅ => regBlock (Q s₅) 0 = Spec.Aes.cipher R w (regBlock (Q s) 0) ∧
      (∀ r, r ∉ sboxWrites → r ≠ kp → s₅.gpr r = s.gpr r) ∧ Frame [⟨b, 320⟩] s.mem s₅.mem ∧
      s₅.rd = s.rd ∧ s₅.wr = s.wr ∧ s₅.sp = s.sp := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hb : s.gpr sb = b := by rw [keep sb (by decide) (by decide) (by decide) (by decide), hs.base]
  have a0 : s.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [keep .a0 (by decide) (by decide) (by decide) (by decide)]; exact hs.a0
  have hp : EncPre s X R w :=
    ⟨hs.scr.congr hwr (by rw [hb, hs.base]), by rw [hb]; exact masks_frame hf hs.masks_disj hs.masks,
      hs.rounds, by rw [a0, hb], by rw [a0]; exact keysAt_frame hR hf hs.keys_disj hs.keys⟩
  refine WP.mono (encrypt4_ok hp (inRel_regBlock (Q s))) fun s₅ ⟨hc₅, hin₅⟩ =>
    ⟨regBlock_of_inRel hin₅ (by decide), hc₅.keep, by have := hc₅.frame; rw [hb] at this; exact this,
      hc₅.rd, hc₅.wr, hc₅.sp⟩

/-- On to the next block. -/
theorem next_ok {k : Nat} (hkn : k < n) (hn : 16 * n < 2 ^ 64) {s₆ : State} (a3₆ : s₆.gpr .a3 = D + BitVec.ofNat 64 (16 * k))
    (a4₆ : s₆.gpr .a4 = BitVec.ofNat 64 (n - k))
    (keep₆ : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s₆.gpr r = s₂.gpr r)
    (rd₆ : s₆.rd = s₂.rd) (wr₆ : s₆.wr = s₂.wr) (sp₆ : s₆.sp = s₂.sp)
    (fr₆ : Frame (eRegions b D n) s₂.mem s₆.mem) (st₆ : regBlock (Q s₆) 0 = st (k + 1))
    (data₆ : EcbInv m₀ s₆.mem D n (k + 1) F) :
    WP isa (.block chainNext) s₆ fun s' =>
      isa.eval (.nonzero .a4) s' = some (decide (n - (k + 1) ≠ 0)) ∧ MAt m₀ s₂ b D n st F (k + 1) s' := by
  unfold chainNext
  refine wp_addi (imm := 16) (by decide) fun s₇ u₇ => wp_subi (imm := 1) (by decide)
    fun s₈ u₈ => WP.block_nil ?_
  have a4₈ : s₈.gpr .a4 = BitVec.ofNat 64 (n - (k + 1)) := by
    rw [u₈.gpr, u₇.other _ (by decide), a4₆, ofNat_sub_ofNat' (by omega),
      show n - k - 1 = n - (k + 1) by omega]
  refine ⟨Steps.eval_nonzero_ofNat s₈ .a4 (by omega) a4₈, ⟨by omega, ?_, a4₈, ?_,
    by rw [u₈.rd, u₇.rd, rd₆], by rw [u₈.wr, u₇.wr, wr₆], by rw [u₈.sp, u₇.sp, sp₆],
    by rw [u₈.mem, u₇.mem]; exact fr₆, ?_, by rw [u₈.mem, u₇.mem]; exact data₆⟩⟩
  · rw [u₈.other _ (by decide), u₇.gpr, a3₆, Offset.add_add, show 16 * k + 16 = 16 * (k + 1) by omega]
  · intro r h1 h2 h3 h4
    rw [u₈.other _ h4, u₇.other _ h3, keep₆ r h1 h2 h3 h4]
  · rw [← st₆]
    refine regBlock_congr ?_ ?_
    · show s₈.gpr (q 0) = s₆.gpr (q 0)
      rw [u₈.other _ (by decide), u₇.other _ (by decide)]
    · show s₈.gpr (q 4) = s₆.gpr (q 4)
      rw [u₈.other _ (by decide), u₇.other _ (by decide)]

/-- The loop over the blocks, from a body that takes `MAt` from `k` to `k + 1`. -/
theorem mloop_ok {body : Prog isa} (hn0 : 0 < n)
    (hb : ∀ k < n, ∀ s, MAt m₀ s₂ b D n st F k s → WP isa body s fun s' =>
      isa.eval (.nonzero .a4) s' = some (decide (n - (k + 1) ≠ 0)) ∧ MAt m₀ s₂ b D n st F (k + 1) s')
    {s : State} (hi : MAt m₀ s₂ b D n st F 0 s) :
    WP isa (.loop body (.nonzero .a4)) s (MAt m₀ s₂ b D n st F n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ MAt m₀ s₂ b D n st F k s)
    (fun m s ⟨k, hm, hk, h⟩ => WP.mono (hb k hk s h) fun s' ⟨ev, h'⟩ => ?_) n s
    ⟨0, by omega, hn0, hi⟩
  by_cases hl : n - (k + 1) = 0
  · have e : k + 1 = n := by omega
    exact .inl ⟨by rw [ev]; simp [hl], e ▸ h'⟩
  · exact .inr ⟨by rw [ev]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

/-- The memory after two doubleword stores at `a3`, `0(a3)` and `8(a3)`. -/
theorem store2_mem {s s₆ s₇ : State} {a : Addr} {v₀ v₄ : Reg} (ha : s.gpr .a3 = a) (ha₆ : s₆.gpr .a3 = a)
    (hv₄ : s₆.gpr v₄ = s.gpr v₄)
    (m₆ : s₆.mem = (s.mem.writeW (s.gpr .a3 + BitVec.ofNat 64 0) ((s.gpr v₀).setWidth 32)).writeW
      (s.gpr .a3 + BitVec.ofNat 64 (0 + 4)) ((s.gpr v₀ >>> 32).setWidth 32))
    (m₇ : s₇.mem = (s₆.mem.writeW (s₆.gpr .a3 + BitVec.ofNat 64 8) ((s₆.gpr v₄).setWidth 32)).writeW
      (s₆.gpr .a3 + BitVec.ofNat 64 (8 + 4)) ((s₆.gpr v₄ >>> 32).setWidth 32)) :
    s₇.mem = (s.mem.writeW a (s.gpr v₀)).writeW (a + 8) (s.gpr v₄) := by
  have e12 : a + BitVec.ofNat 64 (8 + 4) = a + 8 + BitVec.ofNat 64 4 := (Offset.add_add _ _ _).symm
  rw [m₇, ha₆, hv₄, m₆, ha, show a + BitVec.ofNat 64 0 = a by simp,
    show a + BitVec.ofNat 64 (0 + 4) = a + BitVec.ofNat 64 4 from rfl, Words64.writeW64_split,
    show a + BitVec.ofNat 64 8 = a + 8 from rfl, e12, Words64.writeW64_split]

variable {iv : Spec.Aes.State}

/-- The data block at `a3` (`D + 16 k`) XORed into the state, from `s₅`. -/
theorem xorIn_ok (hs : ChSetup true s₂ X b D n R w) {k : Nat} {s₅ : State}
    (a3₅ : s₅.gpr .a3 = D + BitVec.ofNat 64 (16 * k)) (hkn : k < n)
    (hD : (⟨D, 16 * n⟩ : Region) ∈ s₅.rd ++ s₅.wr) {P : State → Prop}
    (cont : ∀ s₄, regBlock (Q s₄) 0 = vxor (regBlock (Q s₅) 0) (Spec.Aes.stateAt s₅.mem
        (D + BitVec.ofNat 64 (16 * k))) →
      (∀ r, r ≠ q 0 → r ≠ q 4 → r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₄.gpr r = s₅.gpr r) →
      s₄.mem = s₅.mem → s₄.rd = s₅.rd → s₄.wr = s₅.wr → s₄.sp = s₅.sp → P s₄) :
    WP isa (.block chainXor) s₅ P := by
  have hn := hs.hn
  obtain ⟨n1, _, n3, n4, n5, n6, n7, n8, n9⟩ := q04
  have hA : ∀ d, s₅.gpr .a3 + BitVec.ofNat 64 d = D + BitVec.ofNat 64 (16 * k + d) := fun d => by
    rw [a3₅, Offset.add_add]
  have hin : ∀ d, d + 4 ≤ 16 → InRegions (s₅.rd ++ s₅.wr) (s₅.gpr .a3 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [hA]; exact in_off hD (by omega) hn
  unfold chainXor
  repeat rw [WP.block_append_iff (M := isa)]
  refine WP.mono (Bytes.loadLE64_ok (d := .t2) (tmp := t0) (hi := t1) (n := .a3) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa using hin 0 (by omega)) (by simpa using hin 4 (by omega)))
    fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  refine wp_xor fun s₂' u₂ => WP.block_nil ?_
  have a₁ : s₂'.gpr .a3 = s₅.gpr .a3 := by
    rw [u₂.other _ (Ne.symm n1), g₁ _ (by decide) (by decide) (by decide)]
  refine WP.mono (Bytes.loadLE64_ok (d := .t2) (tmp := t0) (hi := t1) (n := .a3) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [a₁, u₂.rd, u₂.wr, rd₁, wr₁]; exact hin 8 (by omega))
    (by rw [a₁, u₂.rd, u₂.wr, rd₁, wr₁]; exact hin 12 (by omega)))
    fun s₃ ⟨e₃, g₃, m₃, rd₃, wr₃, sp₃⟩ => ?_
  refine wp_xor fun s₄ u₄ => WP.block_nil ?_
  have o₄ : ∀ r, r ≠ q 0 → r ≠ q 4 → r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₄.gpr r = s₅.gpr r :=
    fun r h0 h4 h2 ht0 ht1 => by
      rw [u₄.other _ h4, g₃ _ h2 ht0 ht1, u₂.other _ h0, g₁ _ h2 ht0 ht1]
  refine cont s₄ ?_ o₄ (by rw [u₄.mem, m₃, u₂.mem, m₁]) (by rw [u₄.rd, rd₃, u₂.rd, rd₁])
    (by rw [u₄.wr, wr₃, u₂.wr, wr₁]) (by rw [u₄.sp, sp₃, u₂.sp, sp₁])
  refine regBlock_xor (m := s₅.mem) ?_ ?_
  · show s₄.gpr (q 0) = s₅.gpr (q 0) ^^^ _
    rw [u₄.other _ n3, g₃ _ n4 n6 n7, u₂.gpr, e₁, g₁ _ n4 n6 n7]
    simpa using congrArg (s₅.mem.readW · 64) (hA 0)
  · show s₄.gpr (q 4) = s₅.gpr (q 4) ^^^ _
    rw [u₄.gpr, g₃ _ n5 n8 n9, e₃, u₂.other _ (Ne.symm n3), g₁ _ n5 n8 n9, u₂.mem, m₁, a₁, hA,
      add_off8]

/-- One block of CFB128 encryption. -/
theorem cfbBody_ok (hs : ChSetup true s₂ X b D n R w) {k : Nat} (hkn : k < n) {s : State}
    (hi : MAt m₀ s₂ b D n (cfbSt R w m₀ D iv) (cfbF R w m₀ D iv) k s) :
    WP isa cfbBody s fun s' => isa.eval (.nonzero .a4) s' = some (decide (n - (k + 1) ≠ 0)) ∧
      MAt m₀ s₂ b D n (cfbSt R w m₀ D iv) (cfbF R w m₀ D iv) (k + 1) s' := by
  have hn := hs.hn
  obtain ⟨_, _, _, _, _, n6, n7, n8, n9⟩ := q04
  unfold cfbBody
  refine WP.seq (WP.mono (enc_ok hs hi.keep hi.wr hi.frame) fun s₅ ⟨st₅, keep₅, fr₅, rd₅, wr₅, sp₅⟩ => ?_)
  have a3₅ : s₅.gpr .a3 = D + BitVec.ofNat 64 (16 * k) := (keep₅ .a3 (by decide) (by decide)).trans hi.a3
  have hD : (⟨D, 16 * n⟩ : Region) ∈ s₅.rd ++ s₅.wr := by rw [rd₅, wr₅, hi.rd, hi.wr]; exact hs.rdD
  have data₅ : EcbInv m₀ s₅.mem D n k (cfbF R w m₀ D iv) :=
    ecbInv_frame fr₅ (by simpa using hs.d320) hn hi.data
  have orig : Spec.Aes.stateAt s₅.mem (D + BitVec.ofNat 64 (16 * k)) =
      Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * k)) := ecbInv_orig data₅ (Nat.le_refl _) hkn
  rw [WP.block_append_iff (M := isa), WP.block_append_iff (M := isa)]
  refine xorIn_ok hs a3₅ hkn hD fun s₄ st₄ o₄ mem₄ rd₄ wr₄ sp₄ => ?_
  rw [st₅, hi.st, orig] at st₄
  have keep₄ : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s₄.gpr r = s₂.gpr r := fun r h1 h2 h3 h4 => by
    rw [o₄ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))
      (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)), keep₅ r h1 h2, hi.keep r h1 h2 h3 h4]
  have a3₄ : s₄.gpr .a3 = D + BitVec.ofNat 64 (16 * k) := by
    rw [o₄ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a3₅
  -- The new state stored over the block.
  unfold chainOut
  repeat rw [WP.block_append_iff (M := isa)]
  have hDw : (⟨D, 16 * n⟩ : Region) ∈ s₄.wr := by rw [wr₄, wr₅, hi.wr]; exact hs.dat rfl
  have hinw : ∀ {t : State} (d : Nat), t.gpr .a3 = D + BitVec.ofNat 64 (16 * k) → t.wr = s₄.wr →
      d + 4 ≤ 16 → InRegions t.wr (t.gpr .a3 + BitVec.ofNat 64 d) 4 := fun d ha hw hd => by
    rw [ha, hw, Offset.add_add]; exact in_off hDw (by omega) hn
  refine WP.mono (Bytes.storeLE64_ok (v := q 0) (tmp := t0) (hi := t1) (n := .a3) (off := 0)
    (Ne.symm n6) (by decide) (by decide) (by decide) (by decide)
    (by simpa using hinw 0 a3₄ rfl (by omega)) (hinw 4 a3₄ rfl (by omega)))
    fun s₆ ⟨m₆, g₆, rd₆, wr₆, sp₆⟩ => ?_
  have a3₆ : s₆.gpr .a3 = D + BitVec.ofNat 64 (16 * k) := (g₆ _ (by decide) (by decide)).trans a3₄
  refine WP.mono (Bytes.storeLE64_ok (v := q 4) (tmp := t0) (hi := t1) (n := .a3) (off := 8)
    (Ne.symm n8) (by decide) (by decide) (by decide) (by decide)
    (hinw 8 a3₆ wr₆ (by omega)) (hinw 12 a3₆ wr₆ (by omega)))
    fun s₇ ⟨m₇, g₇, rd₇, wr₇, sp₇⟩ => ?_
  have hm := store2_mem a3₄ a3₆ (g₆ _ n8 n9) m₆ m₇
  have hst := ecbInv_step (F := cfbF R w m₀ D iv) (m := s₄.mem) (v₁ := s₄.gpr (q 0)) (v₂ := s₄.gpr (q 4))
    (by omega) hkn (by rw [mem₄]; exact data₅) (regBlock_bytes (v := cfbF R w m₀ D iv k) st₄)
  rw [← hm] at hst
  have o₇ : ∀ r, r ≠ t0 → r ≠ t1 → s₇.gpr r = s₄.gpr r := fun r h0 h1 => by rw [g₇ r h0 h1, g₆ r h0 h1]
  refine next_ok hkn hn (by rw [o₇ _ (by decide) (by decide)]; exact a3₄)
    (by rw [o₇ _ (by decide) (by decide), o₄ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      keep₅ _ (by decide) (by decide)]; exact hi.a4)
    (fun r h1 h2 h3 h4 => by
      rw [o₇ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))]; exact keep₄ r h1 h2 h3 h4)
    (by rw [rd₇, rd₆, rd₄, rd₅, hi.rd]) (by rw [wr₇, wr₆, wr₄, wr₅, hi.wr])
    (by rw [sp₇, sp₆, sp₄, sp₅, hi.sp])
    ((hi.frame.trans (fr₅.mono fun r hr => by simp at hr; simp [hr])).trans
      (by rw [← mem₄]; exact hst.2.mono fun r hr => by simp at hr; simp [hr]))
    (by rw [regBlock_congr (Q := Q s₄) (o₇ _ n6 n7) (o₇ _ n8 n9)]; exact st₄)
    hst.1

/-- One block of OFB. -/
theorem ofbBody_ok (hs : ChSetup true s₂ X b D n R w) {k : Nat} (hkn : k < n) {s : State}
    (hi : MAt m₀ s₂ b D n (ofbSt R w m₀ D iv) (ofbF R w m₀ D iv) k s) :
    WP isa ofbBody s fun s' => isa.eval (.nonzero .a4) s' = some (decide (n - (k + 1) ≠ 0)) ∧
      MAt m₀ s₂ b D n (ofbSt R w m₀ D iv) (ofbF R w m₀ D iv) (k + 1) s' := by
  have hn := hs.hn
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := q04
  unfold ofbBody
  refine WP.seq (WP.mono (enc_ok hs hi.keep hi.wr hi.frame) fun s₅ ⟨st₅, keep₅, fr₅, rd₅, wr₅, sp₅⟩ => ?_)
  rw [hi.st] at st₅
  have a3₅ : s₅.gpr .a3 = D + BitVec.ofNat 64 (16 * k) := (keep₅ .a3 (by decide) (by decide)).trans hi.a3
  have hD : (⟨D, 16 * n⟩ : Region) ∈ s₅.rd ++ s₅.wr := by rw [rd₅, wr₅, hi.rd, hi.wr]; exact hs.rdD
  have hDw : (⟨D, 16 * n⟩ : Region) ∈ s₅.wr := by rw [wr₅, hi.wr]; exact hs.dat rfl
  have data₅ : EcbInv m₀ s₅.mem D n k (ofbF R w m₀ D iv) :=
    ecbInv_frame fr₅ (by simpa using hs.d320) hn hi.data
  have orig : Spec.Aes.stateAt s₅.mem (D + BitVec.ofNat 64 (16 * k)) =
      Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * k)) := ecbInv_orig data₅ (Nat.le_refl _) hkn
  have hA : ∀ d, s₅.gpr .a3 + BitVec.ofNat 64 d = D + BitVec.ofNat 64 (16 * k + d) := fun d => by
    rw [a3₅, Offset.add_add]
  have hin : ∀ d, d + 4 ≤ 16 → InRegions (s₅.rd ++ s₅.wr) (s₅.gpr .a3 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [hA]; exact in_off hD (by omega) hn
  have hinw : ∀ d, d + 4 ≤ 16 → InRegions s₅.wr (s₅.gpr .a3 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [hA]; exact in_off hDw (by omega) hn
  rw [WP.block_append_iff (M := isa)]
  unfold ofbXor
  repeat rw [WP.block_append_iff (M := isa)]
  -- The first doubleword.
  refine WP.mono (Bytes.loadLE64_ok (d := .t2) (tmp := t0) (hi := t1) (n := .a3) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa using hin 0 (by omega)) (by simpa using hin 4 (by omega)))
    fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  refine wp_xor fun s₂' u₂ => WP.block_nil ?_
  have a₂ : s₂'.gpr .a3 = s₅.gpr .a3 := by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide) (by decide)]
  refine WP.mono (Bytes.storeLE64_ok (v := .t2) (tmp := t0) (hi := t1) (n := .a3) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [a₂, u₂.wr, wr₁]; simpa using hinw 0 (by omega)) (by rw [a₂, u₂.wr, wr₁]; exact hinw 4 (by omega)))
    fun s₃ ⟨m₃, g₃, rd₃, wr₃, sp₃⟩ => ?_
  have a₃ : s₃.gpr .a3 = s₅.gpr .a3 := by rw [g₃ _ (by decide) (by decide), a₂]
  -- The second.
  refine WP.mono (Bytes.loadLE64_ok (d := .t2) (tmp := t0) (hi := t1) (n := .a3) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [a₃, rd₃, wr₃, u₂.rd, u₂.wr, rd₁, wr₁]; exact hin 8 (by omega))
    (by rw [a₃, rd₃, wr₃, u₂.rd, u₂.wr, rd₁, wr₁]; exact hin 12 (by omega)))
    fun s₄ ⟨e₄, g₄, m₄, rd₄, wr₄, sp₄⟩ => ?_
  refine wp_xor fun s₄' u₄ => WP.block_nil ?_
  have a₄ : s₄'.gpr .a3 = s₅.gpr .a3 := by rw [u₄.other _ (by decide), g₄ _ (by decide) (by decide) (by decide), a₃]
  refine WP.mono (Bytes.storeLE64_ok (v := .t2) (tmp := t0) (hi := t1) (n := .a3) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [a₄, u₄.wr, wr₄, wr₃, u₂.wr, wr₁]; exact hinw 8 (by omega))
    (by rw [a₄, u₄.wr, wr₄, wr₃, u₂.wr, wr₁]; exact hinw 12 (by omega)))
    fun s₆ ⟨m₆, g₆, rd₆, wr₆, sp₆⟩ => ?_
  -- What was stored: the block XORed with the state.
  have o₆ : ∀ r, r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₆.gpr r = s₅.gpr r := fun r h2 h0 h1 => by
    rw [g₆ r h0 h1, u₄.other _ h2, g₄ r h2 h0 h1, g₃ r h0 h1, u₂.other _ h2, g₁ r h2 h0 h1]
  generalize hB : D + BitVec.ofNat 64 (16 * k) = B at *
  let v₁ := s₅.mem.readW B 64 ^^^ s₅.gpr (q 0)
  let v₂ := s₅.mem.readW (B + 8) 64 ^^^ s₅.gpr (q 4)
  have t2₂ : s₂'.gpr .t2 = v₁ := by
    rw [u₂.gpr, e₁, g₁ _ n4 n6 n7, a3₅]; simp [v₁]
  have m₃' : s₃.mem = s₅.mem.writeW B v₁ := by
    rw [m₃, a₂, a3₅, t2₂, u₂.mem, m₁, show B + BitVec.ofNat 64 0 = B by simp,
      show B + BitVec.ofNat 64 (0 + 4) = B + BitVec.ofNat 64 4 from rfl, Words64.writeW64_split]
  have hsep : Mem.Sep (B + BitVec.ofNat 64 8) (64 / 8) B (64 / 8) := by
    have h := Offset.sep B (d := 8) (n := 8) (e := 0) (k := 8) (by omega) (by omega) (by omega)
    rw [show B + BitVec.ofNat 64 0 = B by simp] at h
    exact h
  have t2₄ : s₄'.gpr .t2 = v₂ := by
    rw [u₄.gpr, e₄, g₄ _ n5 n8 n9, g₃ _ n8 n9, u₂.other _ n5, g₁ _ n5 n8 n9, a₃, a3₅, m₃',
      Mem.readW_writeW_sep hsep (by decide)]
    rfl
  have hm : s₆.mem = (s₅.mem.writeW B v₁).writeW (B + 8) v₂ := by
    have e12 : B + BitVec.ofNat 64 (8 + 4) = B + 8 + BitVec.ofNat 64 4 := (Offset.add_add _ _ _).symm
    rw [m₆, a₄, a3₅, t2₄, u₄.mem, m₄, m₃', show B + BitVec.ofNat 64 8 = B + 8 from rfl, e12,
      Words64.writeW64_split]
  have stv : regBlock (fun i => if i = 0 then v₁ else v₂) 0 = ofbF R w m₀ D iv k := by
    rw [show ofbF R w m₀ D iv k = vxor (ofbSt R w m₀ D iv (k + 1))
      (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * k))) from rfl, hB, ← orig, show ofbSt R w m₀ D iv (k + 1) = Spec.Aes.cipher R w (ofbSt R w m₀ D iv k) from rfl, ← st₅]
    refine regBlock_xor (m := s₅.mem) ?_ ?_
    · simp [v₁, BitVec.xor_comm]
    · simp [v₂, BitVec.xor_comm]
  have hst := ecbInv_step (F := ofbF R w m₀ D iv) (v₁ := v₁) (v₂ := v₂) (by omega) hkn data₅
    (by simpa using regBlock_bytes stv)
  rw [hB, ← hm] at hst
  refine next_ok hkn hn (by rw [o₆ _ (by decide) (by decide) (by decide)]; exact a3₅.trans hB.symm)
    (by rw [o₆ _ (by decide) (by decide) (by decide), keep₅ _ (by decide) (by decide)]; exact hi.a4)
    (fun r h1 h2 h3 h4 => by
      rw [o₆ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)),
        keep₅ r h1 h2]; exact hi.keep r h1 h2 h3 h4)
    (by rw [rd₆, u₄.rd, rd₄, rd₃, u₂.rd, rd₁, rd₅, hi.rd])
    (by rw [wr₆, u₄.wr, wr₄, wr₃, u₂.wr, wr₁, wr₅, hi.wr])
    (by rw [sp₆, u₄.sp, sp₄, sp₃, u₂.sp, sp₁, sp₅, hi.sp])
    ((hi.frame.trans (fr₅.mono fun r hr => by simp at hr; simp [hr])).trans
      (hst.2.mono fun r hr => by simp at hr; simp [hr]))
    (by rw [regBlock_congr (Q := Q s₅) (o₆ _ n4 n6 n7) (o₆ _ n5 n8 n9)]; exact st₅)
    hst.1

end Loop

/-! ## The whole functions -/

theorem blocksAt_states (m : Mem) (D : Addr) (n : Nat) :
    Spec.Cbc.blocksAt m D n = (Spec.Aes.statesAt m D n).map Vector.toList := by
  simp only [Spec.Cbc.blocksAt, Spec.Aes.statesAt, List.map_map, Function.comp_def, AesCbc.bytesAt_toList]

/-- A chain of the mode `M` whose loop body takes `MAt` from `k` blocks to
`k + 1` with the states `st` and the blocks `F` meets `blockKRISCV64 M`,
when `M` of the blocks is `F`'s and its chaining value `st`'s. -/
theorem modeK_correct (M : AesCbc.Mode) {body : Prog isa}
    (st F : Nat → List Byte → Mem → Addr → Spec.Aes.State → Nat → Spec.Aes.State)
    (hst0 : ∀ R w m₀ D iv, st R w m₀ D iv 0 = iv)
    (hb : ∀ {m₀ s₂ X b D n R w iv}, ChSetup true s₂ X b D n R w → ∀ k < n, ∀ s,
      MAt m₀ s₂ b D n (st R w m₀ D iv) (F R w m₀ D iv) k s → WP isa body s fun s' =>
        isa.eval (.nonzero .a4) s' = some (decide (n - (k + 1) ≠ 0)) ∧
        MAt m₀ s₂ b D n (st R w m₀ D iv) (F R w m₀ D iv) (k + 1) s')
    (hout : ∀ R w m₀ D iv n, M.out R w iv.toList (Spec.Cbc.blocksAt m₀ D n) =
      (List.range n).map fun j => (F R w m₀ D iv j).toList)
    (hch : ∀ R w m₀ D iv n, M.chain R w iv.toList (Spec.Cbc.blocksAt m₀ D n) = (st R w m₀ D iv n).toList)
    {s₀ : State} (hp : (blockKRISCV64 M).pre s₀) :
    WP isa (chainFrame body [] []) s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (blockKRISCV64 M).post s₀ s' := by
  let n := (s₀.gpr .a4).toNat
  let R := (s₀.gpr .a1).toNat
  let St := s₀.gpr .a2
  let D := s₀.gpr .a3
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * (R + 1))
  let iv := Spec.Aes.stateAt s₀.mem St
  have hp' : framePre true (16 * ·) s₀ := hp
  have dDSt : Region.Disjoint ⟨D, 16 * n⟩ ⟨St, 16⟩ := hp.2.2.2.1
  let Res : State → Prop := fun s => regBlock (Q s) 0 = st R w s₀.mem D iv n ∧
    EcbInv s₀.mem s.mem D n n (F R w s₀.mem D iv)
  refine WP.mono (frame_wp (Res := Res) hp' fun s₉ X b hsF => ?_) fun s' ⟨hg, hra, hm⟩ => ⟨hg, hra, ?_⟩
  · have hs : ChSetup true s₉ X b D n R w :=
      { scr := hsF.scr, base := hsF.base, masks := hsF.masks, rdD := hsF.rdD, dat := hsF.dat,
        hn := hsF.hn, sep := hsF.sep, rounds := hsF.rounds, keys := hsF.keys, a0 := hsF.a0 }
    have dD : ∀ r ∈ [(⟨X, 2048⟩ : Region)], Region.Disjoint ⟨D, 16 * n⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hsF.sep
    have mi₀ : MAt s₀.mem s₉ b D n (st R w s₀.mem D iv) (F R w s₀.mem D iv) 0 s₉ :=
      { hk := Nat.zero_le _
        a3 := by rw [hsF.a3]; simp [D]
        a4 := by rw [hsF.a4]; simp [n]
        keep := fun _ _ _ _ _ => rfl
        rd := rfl
        wr := rfl
        sp := rfl
        frame := Frame.refl _ _
        st := hsF.st.trans (hst0 _ _ _ _ _).symm
        data := ecbInv_frame (m₀ := s₀.mem) (m := s₀.mem) (k := 0) hsF.f₀ dD hsF.hn fun i hi => by simp }
    refine WP.block_nil (WP.mono (mloop_ok hsF.hn0 (fun k hk s h => hb hs k hk s h) mi₀)
      fun s c => WP.block_nil ?_)
    exact { base := (c.keep sb (by decide) (by decide) (by decide) (by decide)).trans hsF.base
            ra := c.keep .ra (by decide) (by decide) (by decide) (by decide)
            rd := c.rd
            wr := c.wr
            sp := c.sp
            frame := c.frame.mono fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
              rcases hr with rfl | rfl
              exacts [.inl rfl, .inr (.inr (.inr (.inr rfl)))]
            res := ⟨c.st, c.data⟩ }
  · show Spec.Cbc.blocksAt s'.mem D n = M.out R w (Spec.Aes.bytesAt s₀.mem St 16) (Spec.Cbc.blocksAt s₀.mem D n) ∧
      Spec.Aes.bytesAt s'.mem St 16 = M.chain R w (Spec.Aes.bytesAt s₀.mem St 16) (Spec.Cbc.blocksAt s₀.mem D n)
    rw [AesCbc.bytesAt_toList s₀.mem St]
    rcases hm with ⟨hn0, hmem⟩ | ⟨s, ⟨hst, hdat⟩, hmem⟩
    · rw [hmem, show n = 0 from hn0, show Spec.Cbc.blocksAt s₀.mem D 0 = [] from rfl, M.out_nil,
        M.chain_nil, ← AesCbc.bytesAt_toList]
      exact ⟨rfl, rfl⟩
    have n16 : 16 * n < 2 ^ 64 := by
      refine Nat.lt_of_not_le fun hc => dDSt St ?_ (by simp [Region.Contains])
      simp only [Region.Contains]
      have := (St - D).isLt
      omega
    have hd : EcbInv s₀.mem s'.mem D n n (F R w s₀.mem D iv) := by
      rw [hmem]
      refine ecbInv_frame (frame_writeW2 _ _ _ _) (fun r hr => ?_) n16 hdat
      simp only [List.mem_singleton] at hr; subst hr; exact dDSt
    refine ⟨?_, ?_⟩
    · rw [hout, blocksAt_states, statesAt_of_ecbInv hd, List.map_map]; rfl
    · rw [hmem, bytesAt_writeW2 _ _ _ _ (regBlock_bytes hst), hch]

theorem cfbChain_correct {s₀ : State} (hp : (blockKRISCV64 (AesCfb.cfbMode true)).pre s₀) :
    WP isa cfbChain s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (blockKRISCV64 (AesCfb.cfbMode true)).post s₀ s' :=
  modeK_correct _ cfbSt cfbF (fun _ _ _ _ _ => rfl) (fun hs _ hk _ h => cfbBody_ok hs hk h)
    (fun R w m₀ D iv n => by
      rw [AesCfb.cfbMode_out, AesCfb.cfb, ite_eq_left rfl,
        ← List.take_of_length_le (l := Spec.Cbc.blocksAt m₀ D n) (i := n) (by simp [Spec.Cbc.blocksAt]),
        cfb_encrypt_eq R w m₀ D iv n (Nat.le_refl _)])
    (fun R w m₀ D iv n => by
      rw [AesCfb.cfbMode_chain, AesCbc.cts, ite_eq_left rfl, AesCfb.cfbMode_out, AesCfb.cfb, ite_eq_left rfl,
        ← List.take_of_length_le (l := Spec.Cbc.blocksAt m₀ D n) (i := n) (by simp [Spec.Cbc.blocksAt]),
        cfb_encrypt_eq R w m₀ D iv n (Nat.le_refl _)]
      exact next_range (fun j => (cfbSt R w m₀ D iv j).toList) n)
    hp

theorem ofbChain_correct {s₀ : State} (hp : (blockKRISCV64 AesOfb.ofbMode).pre s₀) :
    WP isa ofbChain s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (blockKRISCV64 AesOfb.ofbMode).post s₀ s' :=
  modeK_correct _ ofbSt ofbF (fun _ _ _ _ _ => rfl) (fun hs _ hk _ h => ofbBody_ok hs hk h)
    (fun R w m₀ D iv n => by
      rw [AesOfb.ofbMode_out,
        ← List.take_of_length_le (l := Spec.Cbc.blocksAt m₀ D n) (i := n) (by simp [Spec.Cbc.blocksAt]),
        ofb_crypt_eq R w m₀ D iv n (Nat.le_refl _)])
    (fun R w m₀ D iv n => by
      rw [AesOfb.ofbMode_chain, show (Spec.Cbc.blocksAt m₀ D n).length = n by simp [Spec.Cbc.blocksAt],
        ofb_next_eq R w m₀ D iv n])
    hp

/-! ## Constant time, and the calls -/

theorem cfbChain_ct : ConstantTime isa (blockKRISCV64 (AesCfb.cfbMode true)).pre
    (blockKRISCV64 (AesCfb.cfbMode true)).pub cfbChain :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
    (chain_agree true) (by taint_decide)

theorem ofbChain_ct : ConstantTime isa (blockKRISCV64 AesOfb.ofbMode).pre
    (blockKRISCV64 AesOfb.ofbMode).pub ofbChain :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
    (chain_agree true) (by taint_decide)

/-- A chain with `blockKRISCV64 M`'s contract, as a chain to call. -/
theorem blockK_k {M : AesCbc.Mode} {c : Prog isa}
    (hc : ∀ {s₀ : State}, (blockKRISCV64 M).pre s₀ → WP isa c s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ (blockKRISCV64 M).post s₀ s')
    (ct : ConstantTime isa (blockKRISCV64 M).pre (blockKRISCV64 M).pub c) (nf : c.noFrames = true) :
    AesCbc.RISCV64.ChainK true (16 * ·) (blockKRISCV64 M) c where
  pre _ h := h
  pub_of _ _ h := h
  correct s hs := by
    obtain ⟨t, s', he, hg, hra, hp⟩ := hc hs
    exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩
  ct := ct
  noFrames := nf
  post {s₀ s t t'} h hg hm ht hp := by
    have g0 := hg .a0 (by simp)
    have g1 := hg .a1 (by simp)
    have g2 := hg .a2 (by simp)
    have g3 := hg .a3 (by simp)
    have g4 := hg .a4 (by simp)
    have edata : Spec.Cbc.blocksAt (AesCbc.RISCV64.chMem s₀) (s₀.gpr .a3) (s₀.gpr .a4).toNat =
        Spec.Cbc.blocksAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat := h.blocks_eq
    simp only [blockKRISCV64, AesCbc.RISCV64.modeRISCV64, g0, g1, g2, g3, g4, hm, ht] at hp ⊢
    rw [h.sch_eq, h.iv_eq, edata] at hp
    exact hp

theorem cfbChain_k : AesCbc.RISCV64.ChainK true (16 * ·) (blockKRISCV64 (AesCfb.cfbMode true)) cfbChain :=
  blockK_k cfbChain_correct cfbChain_ct rfl

theorem ofbChain_k : AesCbc.RISCV64.ChainK true (16 * ·) (blockKRISCV64 AesOfb.ofbMode) ofbChain :=
  blockK_k ofbChain_correct ofbChain_ct rfl

end VG.Proof.Aes.RISCV64
