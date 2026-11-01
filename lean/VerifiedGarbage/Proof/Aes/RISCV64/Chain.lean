module

public import VerifiedGarbage.Proof.Aes.RISCV64.Ecb
public import VerifiedGarbage.Proof.Aes.RISCV64.Prologue
public import VerifiedGarbage.Proof.Aes.RISCV64.Keys
public import VerifiedGarbage.Proof.Aes.RISCV64.ChainFrame
public import VerifiedGarbage.Impl.Aes.RISCV64.Chain
public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.Spec.Cbc.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Aes.RISCV64.Blocks

/-!
# AES chaining on RISC-V

`chain out` (`Impl/Aes/RISCV64/Chain.lean`) chains the `n` blocks at `data`
into the state at `state`, `C := CIPH_K(C ⊕ Mᵢ)` (`Spec.Cmac.chain`), and,
if `out`, writes each chaining value over its block, which is CBC
encryption (`Spec.Cbc.encrypt`) from the state as the IV. Its contract,
`chainRISCV64 out`, has the arguments of `vg_aes_ctr32`.

As `vg_aes_ctr32`'s proof (`Ctr32.lean`): the prologue rounds the scratch
buffer up, saves the callee-saved registers and builds the masks
(`Prologue.lean`), the return address is stored in slot `raSlot` and the
state's address kept in `ra`;
the key loop (`Keys.lean`) bitslices the round keys. Then the state is
loaded into the registers of block 0, whose bytes (`regBlock`, `Ecb.lean`)
are the chaining value `chainSt` before each block: the block is XORed
into them, and `encrypt4` (`Encrypt.lean`) enciphers them, the other three
blocks being whatever the registers hold. If `out`, the new state is stored
over the block, as `Ecb.lean`'s groups store theirs (`EcbInv`). The
epilogue stores the state and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Aes

open VG.RISCV64 in
/-- RISC-V contract for `Impl.Aes.RISCV64.chain out`, with the arguments
`(schedule = a0, rounds = a1, state = a2, data = a3, n = a4, scratch = a5)`:
`state` becomes `Spec.Cmac.chain` of the `n` blocks at `data` from it, and,
if `out`, the blocks become their CBC encryption from it as the IV.

The code may read `schedule` (240 bytes), read and write `state` (16 bytes)
and `scratch` (2048 bytes, whose contents on exit are unspecified), and read
`data` (`16 n` bytes), or, if `out`, read and write it. `data`, `state` and
`scratch` may not overlap each other or the schedule (but `data` the
schedule, if it is only read), and `state` and `data` may not wrap around
the end of the address space. `rounds` is 10, 12 or 14. The pointers,
`rounds` and `n` are public; the key schedule, the state and the data are
secret. -/
def chainRISCV64 (out : Bool) : Contract RISCV64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let state : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, 16 * (s.gpr .a4).toNat⟩
    let scratch : Region := ⟨s.gpr .a5, 2048⟩
    (if out then s.rd = [sched] ∧ s.wr = [state, data, scratch]
      else s.rd = [sched, data] ∧ s.wr = [state, scratch]) ∧
    sched.Disjoint state ∧ sched.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    state.Disjoint scratch ∧ (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .a3).toNat + 16 * (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    let ciph := Spec.Cmac.aesWith (s.gpr .a1).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .a0) (16 * ((s.gpr .a1).toNat + 1)))
    Spec.Aes.bytesAt s'.mem (s.gpr .a2) 16 =
        Spec.Cmac.chain ciph (Spec.Aes.bytesAt s.mem (s.gpr .a2) 16)
          (Spec.Cmac.blocksAt s.mem (s.gpr .a3) 16 (s.gpr .a4).toNat) ∧
      (out = true → Spec.Cbc.blocksAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat =
        Spec.Cbc.encrypt ciph (Spec.Aes.bytesAt s.mem (s.gpr .a2) 16)
          (Spec.Cbc.blocksAt s.mem (s.gpr .a3) (s.gpr .a4).toNat))
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes

/-! ## The chaining values -/

/-- Two states XORed, byte by byte. -/
def vxor (x y : Spec.Aes.State) : Spec.Aes.State := Vector.ofFn fun i => x[i] ^^^ y[i]

/-- The chaining value after `k` of the blocks at `D` in `m₀`, from `iv`. -/
def chainSt (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) : Nat → Spec.Aes.State
  | 0 => iv
  | k + 1 => Spec.Aes.cipher R w (vxor (chainSt R w m₀ D iv k) (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * k))))

theorem toList_vxor (x y : Spec.Aes.State) : (vxor x y).toList = Spec.Cmac.xor x.toList y.toList := by
  apply List.ext_getElem (by simp [vxor, Spec.Cmac.xor])
  intro i h₁ h₂
  simp [vxor, Spec.Cmac.xor]

theorem ofFn_toList (v : Spec.Aes.State) : (Vector.ofFn fun i : Fin 16 => v.toList.getD i.1 0) = v := by
  apply Vector.ext
  intro i hi
  simp [List.getD_eq_getElem?_getD]

/-- `chainSt` is `Spec.Cmac.chain` over the first `k` blocks. -/
theorem chainSt_eq (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) {n : Nat} :
    ∀ k ≤ n, (chainSt R w m₀ D iv k).toList =
      Spec.Cmac.chain (Spec.Cmac.aesWith R w) iv.toList ((Spec.Cmac.blocksAt m₀ D 16 n).take k)
  | 0, _ => by simp [chainSt, Spec.Cmac.chain]
  | k + 1, hk => by
    have ih := chainSt_eq R w m₀ D iv (n := n) k (by omega)
    have ht : (Spec.Cmac.blocksAt m₀ D 16 n).take (k + 1) =
        (Spec.Cmac.blocksAt m₀ D 16 n).take k ++ [Spec.Aes.bytesAt m₀ (D + BitVec.ofNat 64 (16 * k)) 16] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
      simp [Spec.Cmac.blocksAt]
    simp only [Spec.Cmac.chain] at ih ⊢
    rw [ht, List.foldl_append, ← ih]
    simp only [List.foldl_cons, List.foldl_nil, chainSt, Spec.Cmac.aesWith]
    rw [AesCbc.bytesAt_toList, ← toList_vxor, ofFn_toList]

theorem cbcXor_comm (x y : List Byte) : Spec.Cbc.xor x y = Spec.Cmac.xor y x := by
  simp only [Spec.Cbc.xor, Spec.Cmac.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b)

/-- CBC encryption: block `j` becomes the chaining value after it. -/
theorem encrypt_eq (ciph : Spec.Cmac.Cipher) :
    ∀ (xs : List (List Byte)) (c : List Byte), Spec.Cbc.encrypt ciph c xs =
      (List.range xs.length).map fun j => Spec.Cmac.chain ciph c (xs.take (j + 1))
  | [], _ => rfl
  | x :: xs, c => by
    rw [Spec.Cbc.encrypt, encrypt_eq ciph xs, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp only [List.take_succ_cons, Spec.Cmac.chain, List.foldl_cons, Function.comp_def, List.take_zero,
      List.foldl_nil, cbcXor_comm]

/-! ## The registers of block 0 -/

theorem regBlock_xor {Q Q' : Nat → BitVec 64} {m : Mem} {a : Addr}
    (h₀ : Q' 0 = Q 0 ^^^ m.readW a 64) (h₄ : Q' 4 = Q 4 ^^^ m.readW (a + 8) 64) :
    regBlock Q' 0 = vxor (regBlock Q 0) (Spec.Aes.stateAt m a) := by
  apply Vector.ext
  intro i hi
  simp only [regBlock, vxor, Spec.Aes.stateAt, Vector.getElem_ofFn, Fin.getElem_fin, Nat.zero_add]
  refine byte_ext fun j hj => ?_
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_xor]
  by_cases h8 : i < 8
  · have e : 4 * (i / 8) = 0 := by omega
    rw [e, h₀, BitVec.getLsbD_xor, show i % 8 = i by omega, readW_bit m a h8 hj]
  · have e : 4 * (i / 8) = 4 := by omega
    rw [e, h₄, BitVec.getLsbD_xor, readW_bit m _ (show i % 8 < 8 by omega) hj,
      show (8 : Addr) = BitVec.ofNat 64 8 from rfl, Offset.add_add, show 8 + i % 8 = i by omega]

theorem regBlock_of_inRel {Q : Nat → BitVec 64} {T : Nat → Spec.Aes.State} (h : InRel Q T) {c : Nat}
    (hc : c < 4) : regBlock Q c = T c := by
  apply Vector.ext
  intro t ht
  simp only [regBlock, Vector.getElem_ofFn]
  rw [byte_of_inRel h hc ht, getD_eq _ ht]

theorem regBlock_congr {Q Q' : Nat → BitVec 64} (h₀ : Q' 0 = Q 0) (h₄ : Q' 4 = Q 4) :
    regBlock Q' 0 = regBlock Q 0 := by
  apply Vector.ext
  intro i hi
  simp only [regBlock, Vector.getElem_ofFn, Nat.zero_add]
  by_cases h8 : i < 8
  · rw [show i / 8 = 0 by omega, Nat.mul_zero, h₀]
  · rw [show i / 8 = 1 by omega, Nat.mul_one, h₄]

/-- The bytes of the registers of block 0, as `ecbInv_step` takes them. -/
theorem regBlock_bytes {Q : Nat → BitVec 64} {v : Spec.Aes.State} (h : regBlock Q 0 = v) :
    ∀ t < 16, (if t < 8 then (Q 0).extractLsb' (8 * t) 8 else (Q 4).extractLsb' (8 * (t - 8)) 8) =
      v.getD t 0 := by
  intro t ht
  rw [← h, getD_eq _ ht]
  simp only [regBlock, Vector.getElem_ofFn, Nat.zero_add]
  by_cases h8 : t < 8
  · rw [ite_eq_left h8, show t / 8 = 0 by omega, show t % 8 = t by omega, Nat.mul_zero]
  · rw [ite_eq_right h8, show t / 8 = 1 by omega, show t % 8 = t - 8 by omega, Nat.mul_one]

/-! ## The loop -/

/-- What the loop runs with: `s₂` is the state after the round keys are
bitsliced, `X` the scratch buffer (rounded to `b`), `D` the data (`n`
blocks), which is written only if `out`. -/
structure ChSetup (out : Bool) (s₂ : State) (X b D : Addr) (n R : Nat) (w : List Byte) : Prop where
  scr : Scr s₂ X 2048
  base : s₂.gpr sb = b
  masks : MasksAt s₂.mem b allKs
  rdD : (⟨D, 16 * n⟩ : Region) ∈ s₂.rd ++ s₂.wr
  dat : out = true → (⟨D, 16 * n⟩ : Region) ∈ s₂.wr
  hn : 16 * n < 2 ^ 64
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨X, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 64 (1920 - 64 * R)) R w
  a0 : s₂.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R)

/-- The chaining values, as `EcbInv` takes the blocks: block `j` becomes the
chaining value after it. -/
abbrev chainOutF (R : Nat) (w : List Byte) (m₀ : Mem) (D : Addr) (iv : Spec.Aes.State) (j : Nat) :
    Spec.Aes.State := chainSt R w m₀ D iv (j + 1)

/-- After `k` blocks. -/
structure CAt (out : Bool) (m₀ : Mem) (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte)
    (iv : Spec.Aes.State) (k : Nat) (s : State) : Prop where
  hk : k ≤ n
  a3 : s.gpr .a3 = D + BitVec.ofNat 64 (16 * k)
  a4 : s.gpr .a4 = BitVec.ofNat 64 (n - k)
  keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (eRegions b D n) s₂.mem s.mem
  st : regBlock (Q s) 0 = chainSt R w m₀ D iv k
  data : EcbInv m₀ s.mem D n (if out then k else 0) (chainOutF R w m₀ D iv)

section Loop

variable {out : Bool} {m₀ : Mem} {s₂ : State} {X b D : Addr} {n R : Nat} {w : List Byte}
  {iv : Spec.Aes.State}

theorem ChSetup.d320 (hs : ChSetup out s₂ X b D n R w) : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 320⟩ := by
  refine hs.sep.sub_right ?_
  rw [← hs.base, hs.scr.base]
  exact Offset.sub_base X (by have := Align.pad_lt X; omega)

theorem ChSetup.keys_disj (hs : ChSetup out s₂ X b D n R w) :
    ∀ r ∈ eRegions b D n, Region.Disjoint ⟨b + 1024, 960⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact keys_disjoint b
  · refine (hs.sep.sub_right ?_).symm
    rw [← hs.base]
    exact hs.scr.sub (d := 1024) (n := 960) (by omega)

theorem ChSetup.masks_disj (hs : ChSetup out s₂ X b D n R w) : ∀ r ∈ eRegions b D n,
    Region.Disjoint ⟨b + BitVec.ofNat 64 416, 48⟩ r ∧
      Region.Disjoint ⟨b + BitVec.ofNat 64 512, 96⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨Offset.disjoint_base b (by omega) (by omega), Offset.disjoint_base b (by omega) (by omega)⟩
  · rw [← hs.base]
    exact ⟨(hs.sep.sub_right (hs.scr.sub (by omega))).symm,
      (hs.sep.sub_right (hs.scr.sub (by omega))).symm⟩

theorem q04 : q 0 ≠ .a3 ∧ q 4 ≠ .a3 ∧ q 0 ≠ q 4 ∧ q 0 ≠ .t2 ∧ q 4 ≠ .t2 ∧ q 0 ≠ t0 ∧ q 0 ≠ t1 ∧
    q 4 ≠ t0 ∧ q 4 ≠ t1 := by decide

/-- One block: from after `k` blocks to after `k + 1`. -/
theorem chainBody_ok (hs : ChSetup out s₂ X b D n R w) {k : Nat} (hkn : k < n) {s : State}
    (hi : CAt out m₀ s₂ b D n R w iv k s) :
    WP isa (chainBody out) s fun s' =>
      isa.eval (.nonzero .a4) s' = some (decide (n - (k + 1) ≠ 0)) ∧
        CAt out m₀ s₂ b D n R w iv (k + 1) s' := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hn := hs.hn
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := q04
  have hA : ∀ d, s.gpr .a3 + BitVec.ofNat 64 d = D + BitVec.ofNat 64 (16 * k + d) := fun d => by
    rw [hi.a3, Offset.add_add]
  have hD : (⟨D, 16 * n⟩ : Region) ∈ s.rd ++ s.wr := by rw [hi.rd, hi.wr]; exact hs.rdD
  have hin : ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .a3 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [hA]; exact in_off hD (by omega) hn
  unfold chainBody chainXor
  refine WP.seq ?_
  repeat rw [WP.block_append_iff (M := isa)]
  -- The block XORed into the state.
  refine WP.mono (Bytes.loadLE64_ok (d := .t2) (tmp := t0) (hi := t1) (n := .a3) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa using hin 0 (by omega)) (by simpa using hin 4 (by omega)))
    fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  refine wp_xor fun s₂' u₂ => WP.block_nil ?_
  have a₁ : s₂'.gpr .a3 = s.gpr .a3 := by rw [u₂.other _ (Ne.symm n1), g₁ _ (by decide) (by decide) (by decide)]
  refine WP.mono (Bytes.loadLE64_ok (d := .t2) (tmp := t0) (hi := t1) (n := .a3) (off := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [a₁, u₂.rd, u₂.wr, rd₁, wr₁]; exact hin 8 (by omega))
    (by rw [a₁, u₂.rd, u₂.wr, rd₁, wr₁]; exact hin 12 (by omega)))
    fun s₃ ⟨e₃, g₃, m₃, rd₃, wr₃, sp₃⟩ => ?_
  refine wp_xor fun s₄ u₄ => WP.block_nil ?_
  have o₄ : ∀ r, r ≠ q 0 → r ≠ q 4 → r ≠ .t2 → r ≠ t0 → r ≠ t1 → s₄.gpr r = s.gpr r :=
    fun r h0 h4 h2 ht0 ht1 => by
      rw [u₄.other _ h4, g₃ _ h2 ht0 ht1, u₂.other _ h0, g₁ _ h2 ht0 ht1]
  have mem₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃, u₂.mem, m₁]
  have orig : Spec.Aes.stateAt s.mem (D + BitVec.ofNat 64 (16 * k)) =
      Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * k)) :=
    ecbInv_orig hi.data (by split <;> omega) hkn
  have st₄ : regBlock (Q s₄) 0 =
      vxor (chainSt R w m₀ D iv k) (Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * k))) := by
    rw [← hi.st, ← orig]
    refine regBlock_xor (m := s.mem) ?_ ?_
    · show s₄.gpr (q 0) = s.gpr (q 0) ^^^ _
      rw [u₄.other _ n3, g₃ _ n4 n6 n7, u₂.gpr, e₁, g₁ _ n4 n6 n7]
      simpa using congrArg (s.mem.readW · 64) (hA 0)
    · show s₄.gpr (q 4) = s.gpr (q 4) ^^^ _
      rw [u₄.gpr, g₃ _ n5 n8 n9, e₃, u₂.other _ (Ne.symm n3), g₁ _ n5 n8 n9, u₂.mem, m₁, a₁, hA,
        add_off8]
  -- The state enciphered.
  have keep₄ : ∀ r, r ∉ sboxWrites → r ≠ kp → s₄.gpr r = s.gpr r := fun r h1 _ =>
    o₄ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))
      (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))
  have hb₄ : s₄.gpr sb = b := by
    rw [keep₄ sb (by decide) (by decide), hi.keep sb (by decide) (by decide) (by decide) (by decide), hs.base]
  have a0₄ : s₄.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [keep₄ .a0 (by decide) (by decide), hi.keep .a0 (by decide) (by decide) (by decide) (by decide),
      hs.a0]
  have hp : EncPre s₄ X R w :=
    ⟨hs.scr.congr (by rw [u₄.wr, wr₃, u₂.wr, wr₁, hi.wr]) (by rw [hb₄, hs.base]),
      by rw [hb₄, mem₄]; exact masks_frame hi.frame hs.masks_disj hs.masks, hs.rounds,
      by rw [a0₄, hb₄],
      by rw [a0₄, mem₄]; exact keysAt_frame hR hi.frame hs.keys_disj hs.keys⟩
  refine WP.seq (WP.mono (encrypt4_ok hp (inRel_regBlock (Q s₄))) fun s₅ ⟨hc₅, hin₅⟩ => ?_)
  have st₅ : regBlock (Q s₅) 0 = chainSt R w m₀ D iv (k + 1) := by
    rw [regBlock_of_inRel hin₅ (by decide), st₄]; rfl
  have keep₅ : ∀ r, r ∉ sboxWrites → r ≠ kp → s₅.gpr r = s.gpr r := fun r h1 h2 =>
    (hc₅.keep r h1 h2).trans (keep₄ r h1 h2)
  have fr₅ : Frame [⟨b, 320⟩] s.mem s₅.mem := by
    have := hc₅.frame; rw [hb₄, mem₄] at this; exact this
  have rd₅ : s₅.rd = s₂.rd := by rw [hc₅.rd, u₄.rd, rd₃, u₂.rd, rd₁, hi.rd]
  have wr₅ : s₅.wr = s₂.wr := by rw [hc₅.wr, u₄.wr, wr₃, u₂.wr, wr₁, hi.wr]
  have sp₅ : s₅.sp = s₂.sp := by rw [hc₅.sp, u₄.sp, sp₃, u₂.sp, sp₁, hi.sp]
  have a3₅ : s₅.gpr .a3 = D + BitVec.ofNat 64 (16 * k) :=
    (keep₅ .a3 (by decide) (by decide)).trans hi.a3
  have a4₅ : s₅.gpr .a4 = BitVec.ofNat 64 (n - k) := (keep₅ .a4 (by decide) (by decide)).trans hi.a4
  have frame₅ : Frame (eRegions b D n) s₂.mem s₅.mem :=
    hi.frame.trans (fr₅.mono fun r hr => by simp at hr; simp [hr])
  -- On to the next block, after storing the state over this one if `out`.
  have next : ∀ {s₆ : State}, s₆.gpr .a3 = D + BitVec.ofNat 64 (16 * k) →
      s₆.gpr .a4 = BitVec.ofNat 64 (n - k) →
      (∀ r, r ∉ sboxWrites → r ≠ kp → s₆.gpr r = s.gpr r) →
      s₆.rd = s₂.rd → s₆.wr = s₂.wr → s₆.sp = s₂.sp → Frame (eRegions b D n) s₂.mem s₆.mem →
      regBlock (Q s₆) 0 = chainSt R w m₀ D iv (k + 1) →
      EcbInv m₀ s₆.mem D n (if out then k + 1 else 0) (chainOutF R w m₀ D iv) →
      WP isa (.block chainNext) s₆ fun s' =>
        isa.eval (.nonzero .a4) s' = some (decide (n - (k + 1) ≠ 0)) ∧
          CAt out m₀ s₂ b D n R w iv (k + 1) s' := by
    intro s₆ a3₆ a4₆ keep₆ rd₆ wr₆ sp₆ fr₆ st₆ data₆
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
      rw [u₈.other _ h4, u₇.other _ h3, keep₆ r h1 h2,
        hi.keep r h1 h2 h3 h4]
    · rw [← st₆]
      refine regBlock_congr ?_ ?_
      · show s₈.gpr (q 0) = s₆.gpr (q 0)
        rw [u₈.other _ (by decide), u₇.other _ (by decide)]
      · show s₈.gpr (q 4) = s₆.gpr (q 4)
        rw [u₈.other _ (by decide), u₇.other _ (by decide)]
  cases out with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    refine next a3₅ a4₅ keep₅ rd₅ wr₅ sp₅ frame₅ st₅ ?_
    simp only [Bool.false_eq_true, ↓reduceIte] at hi ⊢
    exact ecbInv_frame fr₅ (by simpa using hs.d320) hn hi.data
  | true =>
    simp only [↓reduceIte]
    unfold chainOut
    repeat rw [WP.block_append_iff (M := isa)]
    have hDw : (⟨D, 16 * n⟩ : Region) ∈ s₅.wr := by rw [wr₅]; exact hs.dat rfl
    have hinw : ∀ {t : State} (d : Nat), t.gpr .a3 = D + BitVec.ofNat 64 (16 * k) → t.wr = s₅.wr →
        d + 4 ≤ 16 → InRegions t.wr (t.gpr .a3 + BitVec.ofNat 64 d) 4 := fun d ha hw hd => by
      rw [ha, hw, Offset.add_add]; exact in_off hDw (by omega) hn
    refine WP.mono (Bytes.storeLE64_ok (v := q 0) (tmp := t0) (hi := t1) (n := .a3) (off := 0)
      (Ne.symm n6) (by decide) (by decide) (by decide) (by decide)
      (by simpa using hinw 0 a3₅ rfl (by omega)) (hinw 4 a3₅ rfl (by omega)))
      fun s₆ ⟨m₆, g₆, rd₆, wr₆, sp₆⟩ => ?_
    have a3₆ : s₆.gpr .a3 = D + BitVec.ofNat 64 (16 * k) := (g₆ _ (by decide) (by decide)).trans a3₅
    refine WP.mono (Bytes.storeLE64_ok (v := q 4) (tmp := t0) (hi := t1) (n := .a3) (off := 8)
      (Ne.symm n8) (by decide) (by decide) (by decide) (by decide)
      (hinw 8 a3₆ wr₆ (by omega)) (hinw 12 a3₆ wr₆ (by omega)))
      fun s₇ ⟨m₇, g₇, rd₇, wr₇, sp₇⟩ => ?_
    have v₄ : s₆.gpr (q 4) = s₅.gpr (q 4) := g₆ _ n8 n9
    have hm : s₇.mem = (s₅.mem.writeW (D + BitVec.ofNat 64 (16 * k)) (s₅.gpr (q 0))).writeW
        (D + BitVec.ofNat 64 (16 * k) + 8) (s₅.gpr (q 4)) := by
      generalize hD' : D + BitVec.ofNat 64 (16 * k) = D'
      have e12 : D' + BitVec.ofNat 64 (8 + 4) = D' + 8 + BitVec.ofNat 64 4 :=
        (Offset.add_add _ _ _).symm
      rw [m₇, a3₆, v₄, m₆, a3₅, hD', show D' + BitVec.ofNat 64 0 = D' by simp,
        show D' + BitVec.ofNat 64 (0 + 4) = D' + BitVec.ofNat 64 4 from rfl, Words64.writeW64_split,
        show D' + BitVec.ofNat 64 8 = D' + 8 from rfl, e12, Words64.writeW64_split]
    have hd₀ : EcbInv m₀ s₅.mem D n k (chainOutF R w m₀ D iv) := by
      have h := hi.data
      simp only [↓reduceIte] at h
      exact ecbInv_frame fr₅ (by simpa using hs.d320) hn h
    have hst := ecbInv_step (F := chainOutF R w m₀ D iv) (v₁ := s₅.gpr (q 0)) (v₂ := s₅.gpr (q 4))
      (by omega) hkn hd₀ (regBlock_bytes st₅)
    rw [← hm] at hst
    have o₇ : ∀ r, r ≠ t0 → r ≠ t1 → s₇.gpr r = s₅.gpr r := fun r h0 h1 => by
      rw [g₇ r h0 h1, g₆ r h0 h1]
    refine next (by rw [o₇ _ (by decide) (by decide)]; exact a3₅)
      (by rw [o₇ _ (by decide) (by decide)]; exact a4₅)
      (fun r h1 h2 => by rw [o₇ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))]; exact keep₅ r h1 h2)
      (by rw [rd₇, rd₆]; exact rd₅) (by rw [wr₇, wr₆]; exact wr₅) (by rw [sp₇, sp₆]; exact sp₅)
      (frame₅.trans (hst.2.mono fun r hr => by simp at hr; simp [hr]))
      (by rw [← st₅]; exact regBlock_congr (o₇ _ n6 n7) (o₇ _ n8 n9))
      (by simp only [↓reduceIte]; exact hst.1)

/-- The loop over the blocks. -/
theorem chainLoop_ok (hs : ChSetup out s₂ X b D n R w) (hn0 : 0 < n) {s : State}
    (hi : CAt out m₀ s₂ b D n R w iv 0 s) :
    WP isa (.loop (chainBody out) (.nonzero .a4)) s (CAt out m₀ s₂ b D n R w iv n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ CAt out m₀ s₂ b D n R w iv k s)
    (fun m s ⟨k, hm, hk, h⟩ => WP.mono (chainBody_ok hs hk h) fun s' ⟨ev, h'⟩ => ?_) n s
    ⟨0, by omega, hn0, hi⟩
  by_cases hl : n - (k + 1) = 0
  · have e : k + 1 = n := by omega
    exact .inl ⟨by rw [ev]; simp [hl], e ▸ h'⟩
  · exact .inr ⟨by rw [ev]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

end Loop


/-! ## The whole function -/

/-- The memory after the state is stored back changed only there. -/
theorem frame_writeW2 (m : Mem) (St : Addr) (v₁ v₂ : BitVec 64) :
    Frame [⟨St, 16⟩] m ((m.writeW St v₁).writeW (St + 8) v₂) := by
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simpa using Offset.contains_base St (d := 0) (n := 8) (k := 16) (by omega) (by omega)
  · exact Offset.contains_base St (d := 8) (n := 8) (k := 16) (by omega) (by omega)

theorem correct_chain {out : Bool} {s₀ : State} (hp : (Proof.Aes.chainRISCV64 out).pre s₀) :
    WP isa (Impl.Aes.RISCV64.chain out) s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (Proof.Aes.chainRISCV64 out).post s₀ s' := by
  let n := (s₀.gpr .a4).toNat
  let R := (s₀.gpr .a1).toNat
  let St := s₀.gpr .a2
  let D := s₀.gpr .a3
  let w := Spec.Aes.bytesAt s₀.mem (s₀.gpr .a0) (16 * (R + 1))
  let iv := Spec.Aes.stateAt s₀.mem St
  have hp' : framePre out (16 * ·) s₀ := hp
  have dDSt : Region.Disjoint ⟨D, 16 * n⟩ ⟨St, 16⟩ := hp.2.2.2.1
  let Res : State → Prop := fun s => regBlock (Q s) 0 = chainSt R w s₀.mem D iv n ∧
    EcbInv s₀.mem s.mem D n (if out then n else 0) (chainOutF R w s₀.mem D iv)
  unfold Impl.Aes.RISCV64.chain
  refine WP.mono (frame_wp (Res := Res) hp' fun s₉ X b hsF => ?_) fun s' ⟨hg, hra, hm⟩ => ⟨hg, hra, ?_⟩
  · have hs : ChSetup out s₉ X b D n R w :=
      { scr := hsF.scr, base := hsF.base, masks := hsF.masks, rdD := hsF.rdD, dat := hsF.dat,
        hn := hsF.hn, sep := hsF.sep, rounds := hsF.rounds, keys := hsF.keys, a0 := hsF.a0 }
    have dD : ∀ r ∈ [(⟨X, 2048⟩ : Region)], Region.Disjoint ⟨D, 16 * n⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hsF.sep
    have ci₀ : CAt out s₀.mem s₉ b D n R w iv 0 s₉ :=
      { hk := Nat.zero_le _
        a3 := by rw [hsF.a3]; simp [D]
        a4 := by rw [hsF.a4]; simp [n]
        keep := fun _ _ _ _ _ => rfl
        rd := rfl
        wr := rfl
        sp := rfl
        frame := Frame.refl _ _
        st := hsF.st
        data := by
          have := ecbInv_frame (m₀ := s₀.mem) (m := s₀.mem) (k := 0) (F := chainOutF R w s₀.mem D iv)
            hsF.f₀ dD hsF.hn fun i hi => by simp
          rw [ite_self]; exact this }
    refine WP.block_nil (WP.mono (chainLoop_ok hs hsF.hn0 ci₀) fun s c => WP.block_nil ?_)
    exact { base := (c.keep sb (by decide) (by decide) (by decide) (by decide)).trans hsF.base
            ra := c.keep .ra (by decide) (by decide) (by decide) (by decide)
            rd := c.rd
            wr := c.wr
            sp := c.sp
            frame := c.frame.mono fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
              rcases hr with rfl | rfl
              exacts [.inl rfl, .inr (.inr (.inr rfl))]
            res := ⟨c.st, c.data⟩ }
  · rcases hm with ⟨hn0, hmem⟩ | ⟨s, ⟨hst, hdat⟩, hmem⟩
    · refine ⟨?_, fun _ => ?_⟩
      · show Spec.Aes.bytesAt s'.mem St 16 = Spec.Cmac.chain _ _ (Spec.Cmac.blocksAt s₀.mem D 16 n)
        rw [hmem, show n = 0 from hn0]; rfl
      · show Spec.Cbc.blocksAt s'.mem D n = Spec.Cbc.encrypt _ _ (Spec.Cbc.blocksAt s₀.mem D n)
        rw [hmem, show n = 0 from hn0]; rfl
    refine ⟨?_, fun ho => ?_⟩
    · show Spec.Aes.bytesAt s'.mem St 16 = Spec.Cmac.chain _ (Spec.Aes.bytesAt s₀.mem St 16)
        (Spec.Cmac.blocksAt s₀.mem D 16 n)
      rw [hmem, bytesAt_writeW2 _ _ _ _ (regBlock_bytes hst), chainSt_eq _ _ _ _ _ n (Nat.le_refl _),
        List.take_of_length_le (by simp [Spec.Cmac.blocksAt]), AesCbc.bytesAt_toList]
    · subst ho
      have n16 : 16 * n < 2 ^ 64 := by
        refine Nat.lt_of_not_le fun hc => dDSt St ?_ (by simp [Region.Contains])
        simp only [Region.Contains]
        have := (St - D).isLt
        omega
      have hd₁₄ : EcbInv s₀.mem s'.mem D n n (chainOutF R w s₀.mem D iv) := by
        simp only [↓reduceIte] at hdat
        rw [hmem]
        refine ecbInv_frame (frame_writeW2 _ _ _ _) (fun r hr => ?_) n16 hdat
        simp only [List.mem_singleton] at hr; subst hr; exact dDSt
      show Spec.Cbc.blocksAt s'.mem D n = Spec.Cbc.encrypt _ (Spec.Aes.bytesAt s₀.mem St 16)
        (Spec.Cbc.blocksAt s₀.mem D n)
      have hb : ∀ m : Mem, Spec.Cbc.blocksAt m D n = (Spec.Aes.statesAt m D n).map Vector.toList := by
        intro m
        simp only [Spec.Cbc.blocksAt, Spec.Aes.statesAt, List.map_map, Function.comp_def,
          AesCbc.bytesAt_toList]
      rw [hb, statesAt_of_ecbInv hd₁₄, encrypt_eq, Spec.Cbc.blocksAt, List.length_map, List.length_range,
        List.map_map]
      refine List.map_congr_left fun j hj => ?_
      have hj := List.mem_range.mp hj
      simp only [Function.comp_apply, chainOutF]
      rw [chainSt_eq _ _ _ _ _ (n := n) (j + 1) (by omega), AesCbc.bytesAt_toList]
      rfl

end VG.Proof.Aes.RISCV64
