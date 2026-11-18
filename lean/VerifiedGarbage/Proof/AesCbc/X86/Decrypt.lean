module

public import VerifiedGarbage.Impl.AesCbc.X86.Decrypt
public import VerifiedGarbage.Proof.AesCbc.X86.Verified
public import VerifiedGarbage.Proof.AesCbc.Rounds
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Dec
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Imc
public import VerifiedGarbage.Proof.Aes.X86.AesNi.BlocksLoop
public import VerifiedGarbage.Proof.Aes.X86.AesNi.Blocks
public import VerifiedGarbage.Proof.Aes.X86.Common
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.AesCbc.Decrypt
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.X86.Rev
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.AesCbc.X86.Decrypt
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.Taint

-- separate module: the loops' and memory proofs cost more to check than their imports.

/-!
# AES-CBC decryption with AES-NI on x86 (32-bit)

`Impl.AesCbc.X86.Decrypt.decrypt` meets the contract that the CBC code
around a block function meets (`cbcX86 false`, `verified`), and of the
scratch buffer it writes only the first 240 bytes (`unwritten`).

The blocks are deciphered independently (`aesDec_ok`, of
`vg_aes_decrypt_blocks_aesni`), and each is XORed with the ciphertext block
before it, which `xmm7` holds: `finish` loads a block's ciphertext into
`xmm7` again before it stores the plaintext over it (`finishData_ok`). After
`c` blocks (`Inv`), the first `c` blocks hold the plaintext (`output`) and
the others are unchanged (`DataInv`), and `xmm7` holds ciphertext block
`c - 1` (the chaining value on entry for `c = 0`: `chaining`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.X86.Decrypt

open VG VG.X86 VG.X86.RegUpd
open VG.Impl.AesCbc.X86.Decrypt
open VG.Impl.Aes.X86.AesNi (at_ argOp regs6 loadData aesDec imcKeys)
open VG.Proof.Aes.X86.AesNi
open VG.Proof.Aes.X86 (reg32 in_rd in_reg part_contains part_sub_reg part_sub part_disj addr_zero addr_add)
open VG.Spec.Aes (bytesAt)

/-! ## One instruction at a time, keeping the SSE registers -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, [b + o]` -/
theorem x_ldm {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Wp.Upd s s' d (s.mem.readW (addr B o) 32) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem ⟨b, o⟩) :: is)) s Q :=
  Wp.cons (s' := s.setReg d _) (by simp only [reduceExec, Wp.readSrc_mem hb hin, Option.map_some])
    (k _ (Wp.Upd.setReg _ _ _) (xmm_setReg _ _ _))

theorem x_addi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d (s.gpr d + v) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.flags _ _ _ _ _ _) rfl)

theorem x_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Upd s s' d (s.gpr d - v) → s'.xmm = s.xmm → s'.zf = some (s.gpr d - v == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ (Wp.Upd.flags _ _ _ _ _ _) rfl rfl)

theorem x_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', Wp.Fupd s s' → s'.xmm = s.xmm → s'.cf = some (decide ((s.gpr d).toNat < v.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  Wp.cons rfl (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem x_test {d : Reg}
    (k : ∀ s', Wp.Fupd s s' → s'.xmm = s.xmm → s'.zf = some (s.gpr d &&& s.gpr d == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  Wp.cons rfl (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl)

/-- `movdqu x, [b + o]` -/
theorem x_load {x : XReg} {b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 16)
    (k : WP isa (.block is) (s.setXmm x (s.mem.readW (addr B o) 128)) Q) :
    WP isa (.block (.movdquLoad x (at_ b o) :: is)) s Q :=
  Wp.cons (by simp only [reduceExec, State.load128, ea_at, hb, hin, ↓reduceIte, Option.map_some]) k

/-- `movdqu [b + o], x` -/
theorem x_store {x : XReg} {b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hout : InRegions s.wr (addr B o) 16)
    (k : ∀ s', Wp.Mupd s s' (s.mem.writeW (addr B o) (s.xmm x)) → WP isa (.block is) s' Q) :
    WP isa (.block (.movdquStore (at_ b o) x :: is)) s Q :=
  Wp.cons (s' := { s with mem := s.mem.writeW (addr B o) (s.xmm x) })
    (by simp only [reduceExec, State.store128, ea_at, hb, hout, ↓reduceIte])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-! ## The data -/

theorem st_inj {a b : BitVec 128} (h : st a = st b) : a = b :=
  VG.Proof.Gcm.X86.ext_byte fun i hi => by rw [← getD_st a hi, ← getD_st b hi, h]

/-- The first `c` blocks are `F` of their index, and the others as in `m₀`. -/
def DataInv (m₀ m : Mem) (D : Addr) (n c : Nat) (F : Nat → Spec.Aes.State) : Prop :=
  ∀ k < n, Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * k)) =
    if k < c then F k else Spec.Aes.stateAt m₀ (D + BitVec.ofNat 64 (16 * k))

theorem original_word {m₀ m : Mem} {D : Addr} {n c k : Nat} {F : Nat → Spec.Aes.State}
    (h : DataInv m₀ m D n c F) (hk : k < n) (hc : c ≤ k) :
    m.readW (D + BitVec.ofNat 64 (16 * k)) 128 = m₀.readW (D + BitVec.ofNat 64 (16 * k)) 128 := by
  apply st_inj
  rw [← stateAt_eq, ← stateAt_eq, h k hk, ite_eq_right (by omega_using [hc])]

theorem data_write {m₀ m : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State} {v : BitVec 128}
    (hn : 16 * n ≤ 2 ^ 64) (hc : c < n) (h : DataInv m₀ m D n c F) (hv : st v = F c) :
    DataInv m₀ (m.writeW (D + BitVec.ofNat 64 (16 * c)) v) D n (c + 1) F := by
  intro k hk
  by_cases he : k = c
  · subst he
    rw [stateAt_eq, Mem.readW_writeW_self _ _ 16 _ (by decide), hv, ite_eq_left (by omega_using [])]
  · rw [stateAt_eq, Mem.readW_writeW_sep (Offset.sep D (by omega_using [he]) (by omega_using [hn, hk])
        (by omega_using [hn, hc])) (by decide), ← stateAt_eq, h k hk]
    by_cases hlt : k < c
    · rw [ite_eq_left hlt, ite_eq_left (by omega_using [hlt])]
    · rw [ite_eq_right hlt, ite_eq_right (by omega_using [hlt, he])]

theorem finish_ok (b : XReg) (j : Nat) (s : State) (hb : b ≠ .xmm7)
    (hin : InRegions s.wr (addr (s.gpr .esi) (16 * j)) 16) :
    WP isa (.block (finish b j)) s fun t =>
      t.mem = s.mem.writeW (addr (s.gpr .esi) (16 * j)) (s.xmm b ^^^ s.xmm .xmm7) ∧
      t.xmm .xmm7 = s.mem.readW (addr (s.gpr .esi) (16 * j)) 128 ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ b → r ≠ .xmm7 → t.xmm r = s.xmm r) := by
  have hin' : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (16 * j)) 16 := in_rd hin
  apply WP.of_runBlock
  simp only [finish, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec, isa,
    State.load128, State.store128, ea_at, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, xmm_setXmm,
    hin, hin', hb, XBinOp.eval, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, fun r h1 h2 => ?_⟩
  simp only [h1, h2, ite_false]

/-- A group is stored in order, each block's ciphertext kept for the next. -/
theorem finishData_ok {m₀ : Mem} {D : Addr} {n c : Nat} {F : Nat → Spec.Aes.State}
    {chain : Nat → BitVec 128} (hn : 16 * n ≤ 2 ^ 64)
    (hnext : ∀ k < n, chain (k + 1) = m₀.readW (D + BitVec.ofNat 64 (16 * k)) 128) :
    ∀ (rs : List XReg) (j : Nat) (s : State), rs.Nodup → .xmm7 ∉ rs →
    (∀ k, c + k < n → addr (s.gpr .esi) (16 * k) = D + BitVec.ofNat 64 (16 * (c + k))) →
    c + j + rs.length ≤ n →
    (⟨D, 16 * n⟩ : Region) ∈ s.wr → DataInv m₀ s.mem D n (c + j) F →
    s.xmm .xmm7 = chain (c + j) →
    (∀ k (h : k < rs.length), st (s.xmm rs[k] ^^^ chain (c + j + k)) = F (c + j + k)) →
    WP isa (.block (finishData rs j)) s fun t =>
      DataInv m₀ t.mem D n (c + j + rs.length) F ∧ t.xmm .xmm7 = chain (c + j + rs.length) ∧
      Frame [⟨D, 16 * n⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r, r ≠ .xmm7 → r ∉ rs → t.xmm r = s.xmm r)
  | [], _, s, _, _, _, _, _, hd, hx, _ =>
    WP.block_nil ⟨hd, hx, Frame.refl _ _, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | b :: bs, j, s, hnd, h7, ha, hc, hw, hd, hx, hv => by
    have hb : b ≠ .xmm7 := fun h => h7 (h ▸ List.mem_cons_self)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    have h7' : .xmm7 ∉ bs := fun h => h7 (List.mem_cons_of_mem _ h)
    simp only [List.length_cons] at hc
    obtain ea : addr (s.gpr .esi) (16 * j) = D + BitVec.ofNat 64 (16 * (c + j)) := ha j (by omega_using [hc])
    obtain hin : (⟨D, 16 * n⟩ : Region).Contains (D + BitVec.ofNat 64 (16 * (c + j))) 16 :=
      Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc, hn])
    rw [finishData, WP.block_append_iff]
    refine WP.mono (finish_ok b j s hb (by rw [ea]; exact ⟨_, hw, hin⟩))
      fun t ⟨hm, hx', hg', hr, hw', ho⟩ => ?_
    rw [ea] at hm hx'
    obtain hv0 : st (s.xmm b ^^^ s.xmm .xmm7) = F (c + j) := by
      rw [hx]; exact hv 0 (Nat.zero_lt_succ _)
    have hd' := data_write hn (by omega_using [hc]) hd hv0
    rw [← hm] at hd'
    obtain hchain : t.xmm .xmm7 = chain (c + (j + 1)) := by
      rw [hx', original_word hd (by omega_using [hc]) (Nat.le_refl _), ← hnext (c + j) (by omega_using [hc]),
        Nat.add_assoc]
    obtain hf : Frame [⟨D, 16 * n⟩] s.mem t.mem := by
      rw [hm]; exact (Frame.refl _ _).writeW List.mem_cons_self _ hin
    refine WP.mono (finishData_ok (m₀ := m₀) (D := D) (n := n) (c := c) (F := F) (chain := chain) hn hnext
      bs (j + 1) t (List.nodup_cons.mp hnd).2 h7' (by rw [hg']; exact ha) (by omega_using [hc])
      (by rw [hw']; exact hw) (by rw [← Nat.add_assoc]; exact hd') hchain
      (fun k hk => by
        rw [ho _ (fun h => hbs (h ▸ List.getElem_mem hk)) (fun h => h7' (h ▸ List.getElem_mem hk)),
          show c + (j + 1) + k = c + j + (k + 1) by omega_using []]
        exact hv (k + 1) (Nat.succ_lt_succ hk))) fun u ⟨hu, hx'', hf', hg'', hr', hw'', ho'⟩ => ?_
    obtain he : c + (j + 1) + bs.length = c + j + (b :: bs).length := by
      rw [List.length_cons]; omega_using []
    rw [he] at hu hx''
    exact ⟨hu, hx'', hf.trans hf', hg''.trans hg', hr'.trans hr, hw''.trans hw', fun r h₁ h₂ =>
      (ho' r h₁ (fun h => h₂ (List.mem_cons_of_mem _ h))).trans
        (ho r (fun h => h₂ (h ▸ List.mem_cons_self)) h₁)⟩

/-! ## The invariant -/

/-- The chaining value of block `k`: the one on entry, or ciphertext block
`k - 1`. -/
def chaining (s₀ : State) : Nat → BitVec 128
  | 0 => s₀.mem.readW ((Iv s₀).setWidth 64) 128
  | k + 1 => s₀.mem.readW (blk s₀ k) 128

/-- Plaintext block `k`. -/
def output (s₀ : State) (k : Nat) : Spec.Aes.State :=
  Vector.ofFn fun i =>
    (Spec.Aes.invCipher (R s₀) (wK s₀) (Spec.Aes.stateAt s₀.mem (blk s₀ k))).getD i.1 0 ^^^
      byte (chaining s₀ k) i.1

/-- The first 240 bytes of the scratch buffer. -/
abbrev scr240 (s₀ : State) : Region := ⟨(S s₀).setWidth 64, 240⟩

/-- After `c` blocks, with `esi` and `edi` at block `p`. -/
structure Inv (s₀ : State) (c p : Nat) (s : State) : Prop where
  le : c ≤ N s₀
  keys : DKeys (R s₀) (wK s₀) s
  eax : s.gpr .eax = W s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 (R s₀)
  edx : s.gpr .edx = S s₀
  esi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * p)
  edi : s.gpr .edi = BitVec.ofNat 32 (N s₀ - p)
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s.gpr r = s₀.gpr r
  chain : s.xmm .xmm7 = chaining s₀ c
  data : DataInv s₀.mem s.mem ((Dp s₀).setWidth 64) (N s₀) c (output s₀)
  frame : Frame [dataR s₀, scr240 s₀] s₀.mem s.mem
  savedEsi : s.mem.readW (addr (S s₀) 0) 32 = s₀.gpr .esi
  savedEdi : s.mem.readW (addr (S s₀) 4) 32 = s₀.gpr .edi
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- A part of the scratch buffer, which writing the data leaves. -/
theorem scr_keep {m m' : Mem} (hf : Frame [dataR s₀] m m') {o w : Nat} (ho : o + w / 8 ≤ 2176)
    (hw : w / 8 < 2 ^ 64) : m'.readW (addr (S s₀) o) w = m.readW (addr (S s₀) o) w :=
  hf.readW (r := ⟨addr (S s₀) o, w / 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_scr.sub_right (part_sub_reg hp.scr_fit ho)).symm) hw

/-- A part of the key schedule, which writing the data leaves. -/
theorem sch_keep {m m' : Mem} (hf : Frame [dataR s₀] m m') {o : Nat} (ho : o + 16 ≤ 240) :
    m'.readW (addr (W s₀) o) 128 = m.readW (addr (W s₀) o) 128 :=
  hf.readW (r := ⟨addr (W s₀) o, 16⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.sch_data.sub_left (part_sub_reg hp.sch_fit ho)) (by decide)

/-- The round keys are kept by writing the data. -/
theorem keys_stable {s t : State} (h : DKeys (R s₀) (wK s₀) s) (ha : s.gpr .eax = W s₀)
    (hd : s.gpr .edx = S s₀) (hga : t.gpr .eax = s.gpr .eax) (hgd : t.gpr .edx = s.gpr .edx)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame [dataR s₀] s.mem t.mem) :
    DKeys (R s₀) (wK s₀) t := by
  obtain hnr : R s₀ ≤ 14 := h.keys.le
  obtain hea : ∀ o, t.ea (at_ .eax o) = s.ea (at_ .eax o) := fun o => by rw [ea_at, ea_at, hga]
  obtain hed : ∀ o, t.ea (at_ .edx o) = s.ea (at_ .edx o) := fun o => by rw [ea_at, ea_at, hgd]
  obtain hma : ∀ o, o + 16 ≤ 240 →
      t.mem.readW (s.ea (at_ .eax o)) 128 = s.mem.readW (s.ea (at_ .eax o)) 128 := fun o ho => by
    rw [ea_at, ha]; exact sch_keep hp hf ho
  obtain hmd : ∀ o, o + 16 ≤ 240 →
      t.mem.readW (s.ea (at_ .edx o)) 128 = s.mem.readW (s.ea (at_ .edx o)) 128 := fun o ho => by
    rw [ea_at, hd]; exact scr_keep hp hf (by omega_using [ho]) (by decide)
  refine ⟨⟨hnr, fun j hj => by rw [hea, hr, hw]; exact h.keys.keys j hj, fun j hj => ?_⟩,
    fun j h1 h2 => ?_, ?_⟩
  · rw [hea, hma _ (by omega_using [hnr, hj])]; exact h.keys.bytes j hj
  · rw [hed, hr, hw, hmd _ (by omega_using [hnr, h2])]; exact h.imc j h1 h2
  · rw [hed, hr, hw, hmd _ (by decide)]; exact h.last

end


/-! ## The groups of blocks -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- `Inv` is kept by moving `esi` and `edi`, and changing the flags. -/
theorem Inv.move {c p p' : Nat} {s t : State} (hI : Inv s₀ c p s)
    (hg : ∀ r, r ≠ .esi → r ≠ .edi → t.gpr r = s.gpr r)
    (hesi : t.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * p')) (hedi : t.gpr .edi = BitVec.ofNat 32 (N s₀ - p'))
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hx : t.xmm = s.xmm) : Inv s₀ c p' t :=
  { le := hI.le
    keys := keys_stable hp hI.keys hI.eax hI.edx (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide))
      hr hw (by rw [hm]; exact Frame.refl _ _)
    eax := by rw [hg _ (by decide) (by decide), hI.eax]
    ecx := by rw [hg _ (by decide) (by decide), hI.ecx]
    edx := by rw [hg _ (by decide) (by decide), hI.edx]
    esi := hesi
    edi := hedi
    keep := fun r h1 h2 h3 h4 h5 => by rw [hg r h4 h5, hI.keep r h1 h2 h3 h4 h5]
    chain := by rw [hx, hI.chain]
    data := by rw [hm]; exact hI.data
    frame := by rw [hm]; exact hI.frame
    savedEsi := by rw [hm, hI.savedEsi]
    savedEdi := by rw [hm, hI.savedEdi]
    rd := by rw [hr, hI.rd]
    wr := by rw [hw, hI.wr] }

/-- The blocks `c … c + N - 1` (`N` the number of registers) deciphered, XORed
with the blocks before them, and stored. -/
theorem group_ok (rs : List XReg) (hrs : rs = regs6 ∨ rs = [.xmm0]) {c : Nat} {s : State}
    (hc : c + rs.length ≤ N s₀) (hI : Inv s₀ c c s) (after : List Instr) {Q : State → Prop}
    (hQ : ∀ t, Inv s₀ (c + rs.length) c t → WP isa (.block after) t Q) :
    WP isa (group rs after) s Q := by
  obtain ⟨hnd, h6⟩ := Ecb.regs_nodup rs hrs
  obtain h7 : .xmm7 ∉ rs := by rcases hrs with rfl | rfl <;> decide
  have hw := hp.data_fit
  obtain haddr : ∀ k, c + k < N s₀ → addr (s.gpr .esi) (16 * k) = blk s₀ (c + k) := fun k hk => by
    rw [hI.esi, addr_add, addr_eq (by omega_using [hw, hk]), ← Nat.mul_add]
  obtain hdat : dataR s₀ ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  refine WP.seq (WP.mono (loadData_ok .esi rs 0 s hnd (fun k hk => by
    rw [Nat.zero_add, haddr k (by omega_using [hc, hk]), hI.rd, hI.wr]
    exact in_rd ⟨dataR s₀, hdat, Offset.contains_base _ (by omega_using [hc, hk]) (by omega_using [hc, hk, hw])⟩))
    fun u ⟨hl, gl, ml, rl, wl, xl⟩ => ?_)
  obtain hku : DKeys (R s₀) (wK s₀) u := hI.keys.of_frame ⟨gl, ml, rl, wl, xl⟩
  refine WP.seq (WP.mono (aesDec_ok rs hnd h6 hp.rounds u hku (by rw [gl, hI.ecx])) fun v ⟨ha, fa⟩ => ?_)
  obtain gv : v.gpr = s.gpr := fa.gpr.trans gl
  obtain mv : v.mem = s.mem := fa.mem.trans ml
  obtain hx : v.xmm .xmm7 = chaining s₀ c := by
    rw [fa.xmm _ (by simp only [List.mem_cons, not_or]; exact ⟨by decide, h7⟩), xl _ h7, hI.chain]
  rw [WP.block_append_iff]
  refine WP.mono (finishData_ok (m₀ := s₀.mem) (D := (Dp s₀).setWidth 64) (n := N s₀) (c := c)
    (F := output s₀) (chain := chaining s₀) (by omega_using [hw]) (fun _ _ => rfl) rs 0 v hnd h7
    (fun k hk => by rw [gv]; exact haddr k hk) (by omega_using [hc])
    (by rw [fa.wr, wl, hI.wr]; exact hdat) (by rw [Nat.add_zero, mv]; exact hI.data)
    (by rw [Nat.add_zero]; exact hx) (fun k hk => by
      have he := ha _ (List.getElem_mem hk)
      rw [hl k hk, Nat.zero_add, haddr k (by omega_using [hc, hk]), hI.data _ (by omega_using [hc, hk]),
        ite_eq_right (by omega_using [])] at he
      rw [Nat.add_zero]
      apply st_ext
      intro i hi
      rw [getD_st _ hi, byte_xor, ← getD_st _ hi, he, output, getD_ofFn hi]))
    fun t ⟨hd, hchain, hf, hg, hr, hw', ho⟩ => ?_
  rw [Nat.add_zero] at hd hchain
  rw [mv] at hf
  obtain gt : t.gpr = s.gpr := hg.trans gv
  obtain rt : t.rd = s.rd := hr.trans (fa.rd.trans rl)
  obtain wt : t.wr = s.wr := hw'.trans (fa.wr.trans wl)
  exact hQ t
    { le := hc
      keys := keys_stable hp hI.keys hI.eax hI.edx (by rw [gt]) (by rw [gt]) rt wt hf
      eax := by rw [gt]; exact hI.eax
      ecx := by rw [gt]; exact hI.ecx
      edx := by rw [gt]; exact hI.edx
      esi := by rw [gt]; exact hI.esi
      edi := by rw [gt]; exact hI.edi
      keep := by rw [gt]; exact hI.keep
      chain := hchain
      data := hd
      frame := hI.frame.trans (hf.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
      savedEsi := by rw [scr_keep hp hf (by decide) (by decide)]; exact hI.savedEsi
      savedEdi := by rw [scr_keep hp hf (by decide) (by decide)]; exact hI.savedEdi
      rd := rt.trans hI.rd
      wr := wt.trans hI.wr }

/-- `add esi, 16 m; sub edi, m`, after `m` more blocks. -/
theorem advance_ok {rest : List Instr} {c m : Nat} (hc : c + m ≤ N s₀) {s : State}
    (hI : Inv s₀ (c + m) c s) {Q : State → Prop}
    (hQ : ∀ s', Inv s₀ (c + m) (c + m) s' →
      s'.zf = some (decide (N s₀ - (c + m) = 0)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .add .esi (.imm (BitVec.ofNat 32 (16 * m))) :: .alu .sub .edi
      (.imm (BitVec.ofNat 32 m)) :: rest)) s Q := by
  have hw := hp.data_fit
  obtain hn : N s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  obtain e : BitVec.ofNat 32 (N s₀ - c) - BitVec.ofNat 32 m = BitVec.ofNat 32 (N s₀ - (c + m)) := by
    rw [Wp.sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  refine x_addi fun s₁ u₁ x₁ => x_subi fun s₂ u₂ x₂ hz => hQ s₂ ?_ ?_
  · refine hI.move hp (fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1]) ?_ ?_
      (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [x₂, x₁])
    · rw [u₂.other _ (by decide), u₁.gpr, hI.esi, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]
    · rw [u₂.gpr, u₁.other _ (by decide), hI.edi, e]
  · rw [hz, u₁.other _ (by decide), hI.edi, e, Wp.ofNat_beq_zero (by omega_using [hn])]

/-- The six-block body. -/
theorem body6_ok {c : Nat} (hc : c + 6 ≤ N s₀) {s : State} (hI : Inv s₀ c c s) :
    WP isa blocks6 s fun s' => Inv s₀ (c + 6) (c + 6) s' ∧ s'.cf = some (decide (N s₀ - (c + 6) < 6)) := by
  obtain hn : N s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  refine group_ok hp regs6 (.inl rfl) hc hI _ fun s₁ hI₁ => ?_
  refine advance_ok hp (m := 6) hc hI₁ fun s₂ hI₂ _ => ?_
  refine x_cmpi fun s₃ u₃ x₃ hcf => WP.block_nil ⟨?_, ?_⟩
  · exact hI₂.move hp (fun r _ _ => by rw [u₃.gpr]) (by rw [u₃.gpr, hI₂.esi]) (by rw [u₃.gpr, hI₂.edi])
      u₃.mem u₃.rd u₃.wr x₃
  · rw [hcf, hI₂.edi, Wp.toNat_ofNat_lt (by omega_using [hn])]; rfl

/-- The one-block body. -/
theorem body1_ok {c : Nat} (hc : c < N s₀) {s : State} (hI : Inv s₀ c c s) :
    WP isa blocks1 s fun s' => Inv s₀ (c + 1) (c + 1) s' ∧ s'.zf = some (decide (N s₀ - (c + 1) = 0)) := by
  refine group_ok hp [.xmm0] (.inr rfl) hc hI _ fun s₁ hI₁ => ?_
  exact advance_ok hp (m := 1) (rest := []) hc hI₁ fun s₂ hI₂ hz => WP.block_nil ⟨hI₂, hz⟩

theorem test_ok {c : Nat} {s : State} (hI : Inv s₀ c c s) :
    WP isa (.block [.alu .test .edi (.reg .edi)]) s fun s' =>
      Inv s₀ c c s' ∧ s'.zf = some (decide (N s₀ - c = 0)) := by
  obtain hn : N s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  refine x_test fun s' u x hz => WP.block_nil ⟨?_, ?_⟩
  · exact hI.move hp (fun r _ _ => by rw [u.gpr]) (by rw [u.gpr, hI.esi]) (by rw [u.gpr, hI.edi])
      u.mem u.rd u.wr x
  · rw [hz, hI.edi, BitVec.and_self, Wp.ofNat_beq_zero (by omega_using [hn])]

/-- The blocks left after `c₀`, six and then one at a time. -/
theorem tail_ok {c₀ : Nat} {s₁ : State} (hI₁ : Inv s₀ c₀ c₀ s₁)
    (hcf : s₁.cf = some (decide (N s₀ - c₀ < 6))) : WP isa tail s₁ (Inv s₀ (N s₀) (N s₀)) := by
  refine WP.seq (WP.mono (Q := fun s => ∃ c, N s₀ - c < 6 ∧ Inv s₀ c c s) ?_ fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (N s₀ - c₀ < 6)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨c₀, by simpa using h, hI₁⟩
    · let I6 : Nat → State → Prop := fun m s => ∃ c, m = N s₀ - c ∧ c + 6 ≤ N s₀ ∧ Inv s₀ c c s
      have hstep : ∀ m s, I6 m s → WP isa blocks6 s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, N s₀ - c < 6 ∧ Inv s₀ c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I6 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (body6_ok hp hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : N s₀ - (c + 6) < 6
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 6, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 6), by omega_using [hc], c + 6, rfl,
            by omega_using [hlt], hI'⟩
      exact WP.loop (M := isa) I6 hstep (N s₀ - c₀) s₁ ⟨c₀, rfl, by simp at h; omega_using [h], hI₁⟩
  refine WP.seq (WP.mono (test_ok hp hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.ite (decide (N s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = N s₀ := by have := hI₃.le; simp at h; omega_using [this, h]
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = N s₀ - c ∧ c < N s₀ ∧ Inv s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa blocks1 s (fun s' =>
        (eval .ne s' = some false ∧ Inv s₀ (N s₀) (N s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (body1_ok hp hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : N s₀ - (c + 1) = 0
      · have : c + 1 = N s₀ := by omega_using [hc, hlast]
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], N s₀ - (c + 1), by omega_using [hc], c + 1, rfl,
          by omega_using [hlast], hI'⟩
    have hlt : c < N s₀ := by have := hI₃.le; simp at h; omega_using [h]
    exact WP.loop (M := isa) I1 hstep (N s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩

end

/-! ## The prologue -/

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  eax : s.gpr .eax = W s₀
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = S s₀
  esi : s.gpr .esi = Dp s₀
  edi : s.gpr .edi = arg s₀ 4
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm7 : s.xmm .xmm7 = chaining s₀ 0
  frame : Frame [⟨addr (S s₀) 0, 8⟩] s₀.mem s.mem
  savedEsi : s.mem.readW (addr (S s₀) 0) 32 = s₀.gpr .esi
  savedEdi : s.mem.readW (addr (S s₀) 4) 32 = s₀.gpr .edi

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- A part of the first 240 bytes of the scratch buffer. -/
theorem sub240 {a n : Nat} (h : a + n ≤ 240) : Region.Sub ⟨addr (S s₀) a, n⟩ (scr240 s₀) := by
  have := part_sub (b := S s₀) (N := 2176) (a := a) (n := n) (c := 0) (k := 240) hp.scr_fit (by decide)
    (Nat.zero_le _) (by omega_using [h])
  rwa [addr_zero] at this

omit hp in
/-- What changes only the data and the first 240 bytes of the scratch buffer
changes only `Big`. -/
theorem big_of {m m' : Mem} (hf : Frame [dataR s₀, scr240 s₀] m m') : Frame (Big s₀) m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩

theorem frame240 {m m' : Mem} {a n : Nat} (h : a + n ≤ 240) (hf : Frame [⟨addr (S s₀) a, n⟩] m m') :
    Frame [dataR s₀, scr240 s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scr240 s₀, List.mem_cons_of_mem _ List.mem_cons_self, sub240 hp h⟩

/-- An argument, in any state that has the permissions on entry and differs
from it only in the data and the first 240 bytes of the scratch buffer. -/
theorem arg_at {s : State} (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr)
    (hf : Frame [dataR s₀, scr240 s₀] s₀.mem s.mem) {i : Nat} (hi : i < 6) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) (4 + 4 * i)) 4 ∧ s.mem.readW (addr (E s₀) (4 + 4 * i)) 32 = arg s₀ i :=
  ⟨by rw [hr, hw]; exact hp.arg_in hi, hp.arg_keep (big_of hf) hi⟩

theorem prologue_ok : WP isa (.block prologue) s₀ (P1 s₀) := by
  have fS := hp.scr_fit
  obtain hwS : reg32 (S s₀) 2176 ∈ s₀.wr := by
    rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain hwI : reg32 (Iv s₀) 16 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self
  obtain hm : (⟨addr (S s₀) 0, 8⟩ : Region) ∈ [⟨addr (S s₀) 0, 8⟩] := List.mem_singleton_self _
  obtain ⟨in5, -⟩ := arg_at hp (s := s₀) rfl rfl (Frame.refl _ _) (i := 5) (by decide)
  refine x_ldm (B := E s₀) (o := 24) rfl in5 fun s₁ u₁ _ => ?_
  obtain e₁ : s₁.gpr .edx = S s₀ := u₁.gpr
  refine Wp.wp_stm (B := S s₀) (o := 0) e₁ (by rw [u₁.wr]; exact in_reg hwS fS (by decide) (by decide))
    fun s₂ u₂ => ?_
  refine Wp.wp_stm (B := S s₀) (o := 4) ((congrFun u₂.gpr _).trans e₁)
    (by rw [u₂.wr, u₁.wr]; exact in_reg hwS fS (by decide) (by decide)) fun s₃ u₃ => ?_
  obtain esp₃ : s₃.gpr .esp = E s₀ := by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain f₃ : Frame [⟨addr (S s₀) 0, 8⟩] s₀.mem s₃.mem := by
    rw [u₃.mem, u₂.mem, u₁.mem]
    exact ((Frame.refl _ _).writeW hm _ (part_contains fS (by decide) (by decide) (by decide) (by decide))).writeW
      hm _ (part_contains fS (by decide) (by decide) (by decide) (by decide))
  obtain a₃ : ∀ i < 6, s₃.mem.readW (addr (E s₀) (4 + 4 * i)) 32 = arg s₀ i := fun i hi =>
    (arg_at hp rd₃ wr₃ (frame240 hp (by decide) f₃) hi).2
  obtain in₃ : ∀ (t : State), t.rd = s₀.rd → t.wr = s₀.wr → ∀ i < 6,
      InRegions (t.rd ++ t.wr) (addr (E s₀) (4 + 4 * i)) 4 := fun t hr hw i hi => by
    rw [hr, hw]; exact hp.arg_in hi
  refine x_ldm (B := E s₀) (o := 12) esp₃ (in₃ _ rd₃ wr₃ 2 (by decide)) fun s₄ u₄ _ => ?_
  obtain e₄ : s₄.gpr .eax = Iv s₀ := by rw [u₄.gpr]; exact a₃ 2 (by decide)
  refine x_load (B := Iv s₀) (o := 0) e₄
    (by rw [u₄.rd, u₄.wr, rd₃, wr₃]; exact in_rd (in_reg hwI hp.iv_fit (by decide) (by decide))) ?_
  refine x_ldm (B := E s₀) (o := 4) (by rw [gpr_setXmm, u₄.other _ (by decide)]; exact esp₃)
    (by rw [rd_setXmm, wr_setXmm]; exact in₃ _ (u₄.rd.trans rd₃) (u₄.wr.trans wr₃) 0 (by decide))
    fun s₅ u₅ x₅ => ?_
  refine x_ldm (B := E s₀) (o := 8)
    (by rw [u₅.other _ (by decide), gpr_setXmm, u₄.other _ (by decide)]; exact esp₃)
    (in₃ _ (by rw [u₅.rd, rd_setXmm, u₄.rd, rd₃]) (by rw [u₅.wr, wr_setXmm, u₄.wr, wr₃]) 1 (by decide))
    fun s₆ u₆ x₆ => ?_
  refine x_ldm (B := E s₀) (o := 16)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), gpr_setXmm, u₄.other _ (by decide)]; exact esp₃)
    (in₃ _ (by rw [u₆.rd, u₅.rd, rd_setXmm, u₄.rd, rd₃]) (by rw [u₆.wr, u₅.wr, wr_setXmm, u₄.wr, wr₃]) 3 (by decide))
    fun s₇ u₇ x₇ => ?_
  refine x_ldm (B := E s₀) (o := 20)
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), gpr_setXmm,
      u₄.other _ (by decide)]; exact esp₃)
    (in₃ _ (by rw [u₇.rd, u₆.rd, u₅.rd, rd_setXmm, u₄.rd, rd₃])
      (by rw [u₇.wr, u₆.wr, u₅.wr, wr_setXmm, u₄.wr, wr₃]) 4 (by decide))
    fun s₈ u₈ x₈ => WP.block_nil ?_
  obtain m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, mem_setXmm, u₄.mem]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd_setXmm, u₄.rd, rd₃],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr_setXmm, u₄.wr, wr₃], ?_, by rw [m₈]; exact f₃, ?_, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, mem_setXmm, u₄.mem]
    exact a₃ 0 (by decide)
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.mem, mem_setXmm, u₄.mem]
    exact a₃ 1 (by decide)
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      gpr_setXmm, u₄.other _ (by decide), u₃.gpr, u₂.gpr]
    exact e₁
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.mem, u₅.mem, mem_setXmm, u₄.mem]
    exact a₃ 3 (by decide)
  · rw [u₈.gpr, u₇.mem, u₆.mem, u₅.mem, mem_setXmm, u₄.mem]
    exact a₃ 4 (by decide)
  · rw [u₈.other r h5, u₇.other r h4, u₆.other r h2, u₅.other r h1, gpr_setXmm, u₄.other r h1, u₃.gpr, u₂.gpr,
      u₁.other r h3]
  · rw [x₈, x₇, x₆, x₅, xmm_setXmm_self, u₄.mem, addr_zero, chaining]
    exact f₃.readW (r := ivR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.iv_scr.sub_right (part_sub_reg fS (by decide))) (by decide)
  · rw [m₈, u₃.mem, VG.Proof.Aes.X86.rd_wr_ne fS _ _ (N := 2176) (by decide) (by decide) (by decide) (by decide)
      (by decide), u₂.mem, u₁.other _ (by decide), Mem.readW_writeW_self32]
  · rw [m₈, u₃.mem, u₂.gpr, u₁.other _ (by decide), Mem.readW_writeW_self32]

end

/-! ## The round keys -/

theorem xmm_withRegions (s : State) (rd wr : List Region) : (s.withRegions rd wr).xmm = s.xmm := rfl

/-- `DKeys` with the same registers and memory, and more permissions. -/
theorem dkeys_widen {nr : Nat} {w : List Byte} {s t : State} (h : DKeys nr w s) (hg : t.gpr = s.gpr)
    (hm : t.mem = s.mem) (hc : Covers (s.rd ++ s.wr) (t.rd ++ t.wr)) : DKeys nr w t := by
  obtain he : ∀ m, t.ea m = s.ea m := fun m => by simp only [State.ea, hg]
  exact ⟨⟨h.keys.le, fun j hj => by rw [he]; exact hc _ _ (h.keys.keys j hj),
      fun j hj => by rw [he, hm]; exact h.keys.bytes j hj⟩,
    fun j h1 h2 => by rw [he, hm]; exact ⟨hc _ _ (h.imc j h1 h2).1, (h.imc j h1 h2).2⟩,
    by rw [he, hm]; exact ⟨hc _ _ h.last.1, h.last.2⟩⟩

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- The prologue, the round keys through `aesimc`, and `cmp edi, 6`. -/
theorem setup_ok : WP isa (.seq (.block prologue) (.seq imcKeys (.block cmp6))) s₀ fun s =>
    Inv s₀ 0 0 s ∧ s.cf = some (decide (N s₀ < 6)) := by
  have fS := hp.scr_fit
  obtain hnr : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  obtain f₁ : Frame [dataR s₀, scr240 s₀] s₀.mem s₁.mem := frame240 hp (by decide) h₁.frame
  obtain hc₁ : s₁.gpr .ecx = BitVec.ofNat 32 (R s₀) := by
    rw [h₁.ecx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- The round keys, where only the schedule and the scratch buffer's first 2048 bytes are permitted.
  let rd : List Region := [reg32 (W s₀) 240]
  let wr : List Region := [reg32 (S s₀) 2048]
  obtain hwr : Covers wr s₁.wr := Covers.of_sub fun r hr => by
    simp only [wr, List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by rw [h₁.wr, hp.wr]; simp, 0, by simp, by show 0 + 2048 ≤ 2176; decide⟩
  obtain hrd : Covers (rd ++ wr) (s₁.rd ++ s₁.wr) :=
    Covers.append_left (Covers.left (Covers.of_mem fun r hr => by
      simp only [rd, List.mem_singleton] at hr; subst hr
      rw [h₁.rd, hp.rd]; exact List.mem_cons_self)) (Covers.right hwr)
  obtain hs : ImcSetup (s₁.withRegions rd wr) :=
    { sch := by rw [State.withRegions_gpr, h₁.eax]; exact List.mem_cons_self
      scr := by rw [State.withRegions_gpr, h₁.edx]; exact List.mem_singleton_self _
      fitS := by rw [State.withRegions_gpr, h₁.eax]; exact hp.sch_fit
      fitB := by rw [State.withRegions_gpr, h₁.edx]; omega_using [fS]
      sep := by
        rw [State.withRegions_gpr, h₁.eax, h₁.edx]
        exact hp.sch_scr.sub_right (Region.sub_prefix (by decide)) }
  obtain hK₁ : Keys (R s₀) (wK s₀) (s₁.withRegions rd wr) := by
    obtain he : ∀ j, 16 * j + 16 ≤ 240 → (s₁.withRegions rd wr).ea (at_ .eax (16 * j)) =
        (W s₀).setWidth 64 + BitVec.ofNat 64 (16 * j) := fun j hj => by
      rw [ea_at, State.withRegions_gpr, h₁.eax]
      exact addr_eq (by have := hp.sch_fit; omega_using [this, hj])
    refine ⟨by omega_using [hnr], fun j hj => ?_, fun j hj => ?_⟩
    · rw [he j (by omega_using [hnr, hj])]
      exact ⟨reg32 (W s₀) 240, List.mem_cons_self,
        Offset.contains_base _ (by omega_using [hnr, hj]) (by omega_using [hnr, hj])⟩
    · rw [he j (by omega_using [hnr, hj]), State.withRegions_mem]
      have h := byte_roundKey s₁.mem ((W s₀).setWidth 64) (L := 16 * (R s₀ + 1)) (j := j) (by omega_using [hj])
      rw [ofInt_natCast, hp.sched_bytes (big_of f₁)] at h
      exact h
  refine WP.seq (WP.narrow (imcKeys_ok hs hp.rounds (by rw [State.withRegions_gpr]; exact hc₁)) hrd hwr
    fun s₂ rd₂ wr₂ _ hd₂ => ?_)
  obtain hK₂ : DKeys (R s₀) (wK s₀) s₂ :=
    dkeys_widen (dKeys_of_imc hs hK₁ hd₂) (State.withRegions_gpr ..).symm (State.withRegions_mem ..).symm
      (by rw [State.withRegions_rd, State.withRegions_wr, rd₂, wr₂]; exact hrd)
  obtain ⟨Sk, hI₂, -, -⟩ := hd₂
  obtain g₂ : s₂.gpr = s₁.gpr := hI₂.gpr
  obtain m₂ : Frame [⟨addr (S s₀) 16, 224⟩] s₁.mem s₂.mem := by
    have := hI₂.frame
    rwa [State.withRegions_gpr, h₁.edx] at this
  obtain x₂ : s₂.xmm .xmm7 = s₁.xmm .xmm7 := hI₂.xmm _ (by decide)
  obtain f₂ : Frame [dataR s₀, scr240 s₀] s₀.mem s₂.mem := f₁.trans (frame240 hp (by decide) m₂)
  obtain k₂ : Frame [scr240 s₀] s₀.mem s₂.mem :=
    (h₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, sub240 hp (by decide)⟩).trans
    (m₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, sub240 hp (by decide)⟩)
  obtain sv₂ : ∀ o, o + 4 ≤ 8 → s₂.mem.readW (addr (S s₀) o) 32 = s₁.mem.readW (addr (S s₀) o) 32 :=
    fun o ho => m₂.readW (r := ⟨addr (S s₀) o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj fS (by omega_using [ho]) (by decide) (.inl (by omega_using [ho]))) (by decide)
  refine x_cmpi fun s₃ u₃ x₃ hcf => WP.block_nil ⟨?_, ?_⟩
  · exact
      { le := Nat.zero_le _
        keys := dkeys_widen hK₂ u₃.gpr u₃.mem (by rw [u₃.rd, u₃.wr]; exact Covers.refl _)
        eax := by rw [u₃.gpr, g₂, h₁.eax]
        ecx := by rw [u₃.gpr, g₂, hc₁]
        edx := by rw [u₃.gpr, g₂, h₁.edx]
        esi := by rw [u₃.gpr, g₂, h₁.esi, Nat.mul_zero, BitVec.add_zero]
        edi := by rw [u₃.gpr, g₂, h₁.edi, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        keep := by rw [u₃.gpr, g₂]; exact h₁.keep
        chain := by rw [x₃, x₂, h₁.xmm7]
        data := fun k hk => by
          rw [u₃.mem, ite_eq_right (Nat.not_lt_zero _), stateAt_eq, stateAt_eq]
          exact congrArg st <| k₂.readW (r := ⟨blk s₀ k, 16⟩) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide)))
            (by decide)
        frame := by rw [u₃.mem]; exact f₂
        savedEsi := by rw [u₃.mem, sv₂ 0 (by decide), h₁.savedEsi]
        savedEdi := by rw [u₃.mem, sv₂ 4 (by decide), h₁.savedEdi]
        rd := by rw [u₃.rd, rd₂, h₁.rd]
        wr := by rw [u₃.wr, wr₂, h₁.wr] }
  · rw [hcf, g₂, h₁.edi]; rfl

end

/-! ## The mode -/

theorem list_getD {α : Type} {xs : List α} {k : Nat} {d : α} (hk : k < xs.length) : xs.getD k d = xs[k] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

theorem vector_listD (v : Spec.Aes.State) (i : Nat) (hi : i < 16) : v.toList.getD i 0 = v.getD i 0 := by
  rw [list_getD (by simpa using hi), Vector.getElem_toList]
  simp [Vector.getD, hi]

theorem chaining_bytes (s₀ : State) (k : Nat) (hk : k ≤ N s₀) :
    (st (chaining s₀ k)).toList = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
  cases k with
  | zero => simp only [chaining, ← stateAt_eq, List.take_zero]; exact (bytesAt_toList _ _).symm
  | succ k =>
    rw [next_take_succ _ _ k (by rw [length_blocksAt]; omega_using [hk]),
      list_getD (by rw [length_blocksAt]; omega_using [hk]), getElem_blocksAt (hk := by omega_using [hk])]
    exact (congrArg Vector.toList (stateAt_eq _ _).symm).trans (bytesAt_toList _ _).symm

theorem block_bytes (s₀ : State) (k : Nat) (hk : k < N s₀) :
    (output s₀ k).toList =
      (Spec.Cbc.decrypt (Spec.Cbc.aesInvWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀)).getD k [] := by
  rw [decrypt_getD _ _ _ k (by rw [length_blocksAt]; exact hk),
    list_getD (by rw [length_blocksAt]; exact hk), getElem_blocksAt (hk := hk),
    aesInvWith_state, ← chaining_bytes _ _ (Nat.le_of_lt hk)]
  apply Proof.Cmac.ext16 (by simp) (by simp [Spec.Cbc.xor])
  intro i hi
  rw [vector_listD _ _ hi, xor_eq, Proof.Cmac.getD_xor (by simp) (by simpa using hi),
    vector_listD _ _ hi, vector_listD _ _ hi, getD_st _ hi]
  exact getD_ofFn hi

theorem data_done {s₀ : State} {m : Mem}
    (hd : DataInv s₀.mem m ((Dp s₀).setWidth 64) (N s₀) (N s₀) (output s₀)) :
    Spec.Cbc.blocksAt m ((Dp s₀).setWidth 64) (N s₀) =
      Spec.Cbc.decrypt (Spec.Cbc.aesInvWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀) := by
  apply List.ext_getElem
  · simp [length_decrypt, length_blocksAt]
  · intro k hk _
    have hk' : k < N s₀ := by simpa [length_blocksAt] using hk
    rw [getElem_blocksAt _ _ hk', bytesAt_toList, hd k hk', ite_eq_left hk', block_bytes _ _ hk',
      list_getD (by simp [length_decrypt, length_blocksAt]; exact hk')]

/-! ## The epilogue -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem epilogue_ok {s : State} (hI : Inv s₀ (N s₀) (N s₀) s) :
    WP isa (.block epilogue) s fun t =>
      abiPreserved s₀ t ∧ (cbcX86 false).post s₀ t ∧ Frame [ivR s₀, dataR s₀, scr240 s₀] s₀.mem t.mem := by
  have fS := hp.scr_fit
  obtain ⟨in2, a2⟩ := arg_at hp hI.rd hI.wr hI.frame (i := 2) (by decide)
  obtain hesp : s.gpr .esp = E s₀ := hI.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain hwI : reg32 (Iv s₀) 16 ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self
  obtain hwS : reg32 (S s₀) 2176 ∈ s₀.wr := by
    rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine x_ldm (B := E s₀) (o := 12) hesp in2 fun s₁ u₁ x₁ => ?_
  obtain e₁ : s₁.gpr .eax = Iv s₀ := by rw [u₁.gpr]; exact a2
  refine x_store (B := Iv s₀) (o := 0) e₁
    (by rw [u₁.wr, hI.wr]; exact in_reg hwI hp.iv_fit (by decide) (by decide)) fun s₂ u₂ => ?_
  obtain edx₂ : s₂.gpr .edx = S s₀ := by rw [u₂.gpr, u₁.other _ (by decide), hI.edx]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, hI.wr]
  refine Wp.wp_ldm (B := S s₀) (o := 0) edx₂ (by rw [wr₂]; exact in_rd (in_reg hwS fS (by decide) (by decide)))
    fun s₃ u₃ => ?_
  refine Wp.wp_ldm (B := S s₀) (o := 4) (by rw [u₃.other _ (by decide)]; exact edx₂)
    (by rw [u₃.wr, wr₂]; exact in_rd (in_reg hwS fS (by decide) (by decide))) fun s₄ u₄ => WP.block_nil ?_
  obtain m₂ : s₂.mem = s.mem.writeW ((Iv s₀).setWidth 64) (s.xmm .xmm7) := by
    rw [u₂.mem, u₁.mem, x₁, addr_zero]
  obtain m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  obtain fs : Frame [ivR s₀] s.mem s₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  obtain G : Frame [ivR s₀, dataR s₀, scr240 s₀] s₀.mem s₂.mem :=
    (hI.frame.mono fun r hr => List.mem_cons_of_mem _ hr).trans (fs.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
  obtain sv : ∀ o, o + 4 ≤ 8 → s₂.mem.readW (addr (S s₀) o) 32 = s.mem.readW (addr (S s₀) o) 32 :=
    fun o ho => fs.readW (r := ⟨addr (S s₀) o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.iv_scr.sub_right (part_sub_reg fS (by omega_using [ho]))).symm) (by decide)
  obtain keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s₄.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₄.other r h5, u₃.other r h4, u₂.gpr, u₁.other r h1, hI.keep r h1 h2 h3 h4 h5]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ⟨?_, ?_⟩, by rw [m₄]; exact G⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [u₄.other _ (by decide), u₃.gpr, sv 0 (by decide), hI.savedEsi]
    · rw [u₄.gpr, u₃.mem, sv 4 (by decide), hI.savedEdi]
    · exact keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [m₄]
    exact G.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_iv
      · exact hp.ret_data
      · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))) (by decide)
  · show Spec.Cbc.blocksAt s₄.mem ((Dp s₀).setWidth 64) (N s₀) = _
    obtain hb : Spec.Cbc.blocksAt s₂.mem ((Dp s₀).setWidth 64) (N s₀) =
        Spec.Cbc.blocksAt s.mem ((Dp s₀).setWidth 64) (N s₀) :=
      List.map_congr_left fun k hk => Proof.Cmac.bytesAt_frame fs (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.iv_data.symm.sub_left (UPre.data_sub (List.mem_range.mp hk))) (by decide)
    rw [m₄, hb, data_done hI.data]
    rfl
  · show bytesAt s₄.mem ((Iv s₀).setWidth 64) 16 = _
    rw [m₄, m₂, bytesAt_toList, stateAt_eq, Mem.readW_writeW_self _ _ 16 _ (by decide), hI.chain,
      chaining_bytes _ _ (Nat.le_refl _), List.take_of_length_le (by rw [length_blocksAt]; exact Nat.le_refl _)]
    rfl

/-- The whole function: the contract, and what it writes. -/
theorem correct_wp : WP isa decrypt s₀ fun t =>
    abiPreserved s₀ t ∧ (cbcX86 false).post s₀ t ∧ Frame [ivR s₀, dataR s₀, scr240 s₀] s₀.mem t.mem := by
  have h := setup_ok hp
  obtain ⟨t₁, s₁, he₁, hq₁⟩ := h
  sorry

end

end VG.Proof.AesCbc.X86.Decrypt
