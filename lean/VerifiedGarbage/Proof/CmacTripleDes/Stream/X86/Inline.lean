module

public import VerifiedGarbage.Impl.CmacTripleDes.X86
public import VerifiedGarbage.Proof.CmacTripleDes.X86.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.CmacTripleDes.X86.Finalize
import VerifiedGarbage.Proof.CmacTripleDes.Words
public import VerifiedGarbage.Proof.CmacTripleDes.Cmac
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
import VerifiedGarbage.Proof.CmacTripleDes.InlineCT
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.X86
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Finalize
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Contract
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Lit
meta import VerifiedGarbage.Impl.CmacTripleDes.X86
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.CmacTripleDes.X86.Update
public import VerifiedGarbage.Proof.CmacTripleDes.X86.Block
import VerifiedGarbage.Proof.CmacTripleDes.KeySchedule
import VerifiedGarbage.Proof.CmacTripleDes.X86.KeysLit
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Update
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Block
meta import VerifiedGarbage.Proof.CmacTripleDes.KeySchedule
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.KeysLit
meta import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.CmacTripleDes.Cmac
meta import VerifiedGarbage.Proof.CmacTripleDes.Words
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `CmacTripleDes.X86.CT`, which only this module used -/

section

/-! ### `CmacTripleDes.X86.Init`, which this module and modules that import it used -/

section

/-! ### `CmacTripleDes.X86.Keys`, which only this module used -/

section

/-!
# DES's key schedule on x86 (32-bit)

Untrusted: everything here is checked by Lean.

`roundKeys` only moves bits of the key at `[esi]` (its high word, then its
low word) to the round keys' words it stores at `[edi]`: the kernel checks it
over the lane domain (`roundKeys_check`, `linear_ok`), and
`getLsbD_expandDesKey` says the bits are the specification's.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.X86
  VG.Proof.CmacTripleDes

/-- The round keys' words at `edi`, and the key's two words at `esi`. -/
def kCfg : Cfg := { base := .edi, slots := 32, ext := .esi, exts := 2 }

/-- Bit `q` of word `w` (0 low, 1 high) of round key `j`: bit `rkSrc j (32 w + q)`
of the key. -/
def rkG (k q : Nat) : List Nat :=
  if q < (if k % 2 = 0 then 32 else 16) then [xAtom (rkSrc (k / 2) (32 * (k % 2) + q))] else []

theorem rkG_lo {j q : Nat} (hq : q < 32) : rkG (2 * j) q = [xAtom (rkSrc j q)] := by
  simp [rkG, hq, show 2 * j / 2 = j by omega_using []]

theorem rkG_hi {j q : Nat} (hq : q < 16) : rkG (2 * j + 1) q = [xAtom (rkSrc j (32 + q))] := by
  simp [rkG, hq, show (2 * j + 1) % 2 = 1 by omega_using [], show (2 * j + 1) / 2 = j by omega_using []]

theorem rkG_hi0 {j q : Nat} (hq : 16 ≤ q) : rkG (2 * j + 1) q = [] := by
  simp [rkG, show (2 * j + 1) % 2 = 1 by omega_using [], show ¬ q < 16 by omega_using [hq]]

/-- Every round key's words. -/
def kOuts : List (Nat × (Nat → List Nat)) := (List.range 32).map fun k => (k, rkG k)

theorem roundKeys_check :
    check (lanes 32 6) kCfg (linExt 0) roundKeys (linEnv []) (linPost kCfg.slots 6 kOuts) = true := by
  rw [roundKeys_eq]; lit_decide

theorem rkSrc_lt : ∀ j < 16, ∀ q < 48, rkSrc j q < 64 := by lit_decide

/-- The registers `roundKeys` keeps. -/
def kKept : List Reg := [.eax, .edx, .esi, .edi, .ebp, .esp]

theorem roundKeys_kept : kKept.all (fun r => roundKeys.all fun i => i.dst != some r) = true := by
  rw [roundKeys_eq]; lit_decide

/-- The DES key at `esi`: its high word, then its low word. -/
abbrev desKey (s : State) : BitVec 64 :=
  s.mem.readW (wordAddr (s.gpr .esi) 0) 32 ++ s.mem.readW (wordAddr (s.gpr .esi) 1) 32

/-- The round keys of the DES key at `esi`, in `[edi + 8 j]` and `[edi + 8 j + 4]`. -/
theorem roundKeys_ok {s : State} (hok : Ok kCfg s) :
    ∃ s', runBlock isa roundKeys s = some s' ∧
      (∀ j < 16, (s'.mem.readW (wordAddr (s.gpr .edi) (2 * j + 1)) 32).setWidth 16 ++
          s'.mem.readW (wordAddr (s.gpr .edi) (2 * j)) 32 =
        (Spec.TripleDes.expandDesKey (desKey s)).getD j 0) ∧
      (∀ j < 16, (s'.mem.readW (wordAddr (s.gpr .edi) (2 * j + 1)) 32) >>> 16 = 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kKept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion kCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.mem.readW (wordAddr (s.gpr .esi) 0) 32
    else s.mem.readW (wordAddr (s.gpr .esi) 1) 32
  obtain ⟨s', hs', hout, rd, wr, keep, fr⟩ := linear_ok roundKeys_check hok W (fun j i h => by simp at h)
    (fun j hj => by
      simp only [kCfg] at hj
      rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl
      · exact ⟨by decide, rfl⟩
      · exact ⟨by decide, rfl⟩)
  obtain hw : ∀ k < 32, ∀ q < 32, (s'.mem.readW (wordAddr (s.gpr .edi) k) 32).getLsbD q = xorBits W (rkG k q) :=
    fun k hk q hq => hout k (rkG k) (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩) q hq
  have hx : W 0 ++ W 1 = desKey s := rfl
  refine ⟨s', hs', fun j hj => ?_, fun j hj => ?_, rd, wr,
    fun r hr => keep _ (List.all_eq_true.mp roundKeys_kept r hr), fr⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [BitVec.getLsbD_append, getLsbD_expandDesKey _ hj hq]
    obtain hs := rkSrc_lt j hj q hq
    by_cases h32 : q < 32
    · rw [ite_eq_left h32, hw (2 * j) (by omega_using [hj]) q h32, rkG_lo h32, xorBits_cons, xorBits_nil,
        Bool.xor_false, bit_xAtom W hs, hx]
    · rw [ite_eq_right h32, BitVec.getLsbD_setWidth, decide_eq_true (by omega_using [hq] : q - 32 < 16), Bool.true_and,
        hw (2 * j + 1) (by omega_using [hj]) (q - 32) (by omega_using [hq]), rkG_hi (by omega_using [hq]), show 32 + (q - 32) = q by omega_using [h32],
        xorBits_cons, xorBits_nil, Bool.xor_false, bit_xAtom W hs, hx]
  · apply BitVec.eq_of_getLsbD_eq
    intro q hq
    rw [BitVec.getLsbD_ushiftRight]
    by_cases hq' : 16 + q < 32
    · rw [hw (2 * j + 1) (by omega_using [hj]) (16 + q) hq', rkG_hi0 (by omega_using [])]
      simp
    · rw [BitVec.getLsbD_of_ge _ _ (by omega_using [hq'])]
      simp

end VG.Proof.CmacTripleDes.X86

end

end


/-!
# TDEA-CMAC on x86: `vg_cmac_triple_des_init`

Untrusted: everything here is checked by Lean. `initPre` saves the
registers and stores the three DES keys, as the high and low words of
big-endian integers, at bytes `[100, 124)` of the scratch buffer; each
iteration of the loop then writes one DES key's sixteen round keys
(`KInv`); the zero block is encrypted with them and doubled twice, a word
at a time, into the subkeys.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86 VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_add wp_subi wp_sub wp_andi
  wp_or wp_cmpi wp_shr wp_bswap)
open VG.X86.Straight (wordAddr)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `xor d, r`. -/
theorem wp_xorr {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  Wp.wp_xor fun s' u => k s' ⟨u.gpr, u.other, u.mem, u.rd, u.wr⟩

end

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev K : BitVec 32 := arg s₀ 0
abbrev Kl : Nat := (arg s₀ 1).toNat
abbrev O : BitVec 32 := arg s₀ 2
abbrev Sc : BitVec 32 := arg s₀ 3

abbrev ikeyR : Region := ⟨(K s₀).setWidth 64, Kl s₀⟩
abbrev outR : Region := ⟨(O s₀).setWidth 64, 400⟩
abbrev iscrR : Region := ⟨(Sc s₀).setWidth 64, 640⟩
abbrev iargsR : Region := ⟨argAddr s₀ 0, 16⟩

/-- The key's bytes. -/
abbrev keyB : List Byte := Spec.Aes.bytesAt s₀.mem ((K s₀).setWidth 64) (Kl s₀)

/-- DES key `j`, as a big-endian integer. -/
abbrev kw (j : Nat) : BitVec 64 :=
  byteRev64 (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) j)) 64)

/-- What the function changes after saving the registers. -/
abbrev ichg : List Region :=
  [⟨(Sc s₀).setWidth 64, 84⟩, ⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 100, 24⟩, outR s₀]

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [ikeyR s₀, iargsR s₀]
  wr : s₀.wr = [outR s₀, iscrR s₀]
  key_out : (ikeyR s₀).Disjoint (outR s₀)
  key_scr : (ikeyR s₀).Disjoint (iscrR s₀)
  out_scr : (outR s₀).Disjoint (iscrR s₀)
  args_out : (iargsR s₀).Disjoint (outR s₀)
  args_scr : (iargsR s₀).Disjoint (iscrR s₀)
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_scr : (retR s₀).Disjoint (iscrR s₀)
  key_fit : (K s₀).toNat + Kl s₀ ≤ 2 ^ 32
  out_fit : (O s₀).toNat + 400 ≤ 2 ^ 32
  scr_fit : (Sc s₀).toNat + 640 ≤ 2 ^ 32
  esp_fit : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32
  valid : Kl s₀ = 16 ∨ Kl s₀ = 24

theorem IPre.of {s₀ : State} (h : initX86.pre s₀) : IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n⟩

/-- After the round keys of `i` DES keys. -/
structure KInv (s₀ : State) (i : Nat) (s : State) : Prop where
  ebp : s.gpr .ebp = Sc s₀
  esi : s.gpr .esi = Sc s₀ + BitVec.ofNat 32 (100 + 8 * i)
  edi : s.gpr .edi = O s₀ + BitVec.ofNat 32 (128 * i)
  edx : s.gpr .edx = BitVec.ofNat 32 (3 - i)
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keys : ∀ j < 3, s.mem.readW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 (100 + 8 * j)) 32 ++
    s.mem.readW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 (104 + 8 * j)) 32 = kw s₀ j
  sched : ∀ n < 16 * i, s.mem.readW ((O s₀).setWidth 64 + BitVec.ofNat 64 (8 * n)) 64 =
    (Spec.TripleDes.expandKey (keyB s₀)).getD n 0
  frame : Frame [⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 100, 24⟩, ⟨(O s₀).setWidth 64, 384⟩]
    (savedMem s₀ (Sc s₀)) s.mem

/-! ## Regions -/

theorem keyOff_le {s₀ : State} (hp : IPre s₀) {j : Nat} (hj : j < 3) : keyOff (Kl s₀) j + 8 ≤ Kl s₀ := by
  simp only [keyOff]; rcases hp.valid with h | h <;> rw [h] <;> split <;> omega_arith

section
variable {s₀ : State} (hp : IPre s₀)
include hp

theorem IPre.inScr {d n : Nat} (h : d + n ≤ 640) (_hn : 0 < n) :
    InRegions s₀.wr ((Sc s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := iscrR s₀) (by simp) (Offset.contains_base _ h (by have := hp.scr_fit; omega_arith))

theorem IPre.inOut {d n : Nat} (h : d + n ≤ 400) (_hn : 0 < n) :
    InRegions s₀.wr ((O s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := outR s₀) (by simp) (Offset.contains_base _ h (by have := hp.out_fit; omega_arith))

theorem IPre.inKey {d n : Nat} (h : d + n ≤ Kl s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) ((K s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ikeyR s₀) (by simp) (Offset.contains_base _ h (by have := hp.key_fit; omega_arith))

theorem IPre.scrEa {s : State} (h : s.gpr .ebp = Sc s₀) {d : Nat} (hd : d < 640) :
    s.ea (at_ .ebp d) = (Sc s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [ea_at', h]; exact addr_eq (by have := hp.scr_fit; omega_arith)

theorem IPre.keyEa {s : State} (h : s.gpr .ecx = K s₀) {d : Nat} (hd : d < Kl s₀) :
    s.ea (at_ .ecx d) = (K s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [ea_at', h]; exact addr_eq (by have := hp.key_fit; omega_arith)

theorem IPre.argAddr_eq {i : Nat} (hi : i < 4) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.esp_fit
  show addr (s₀.gpr .esp) (4 + 4 * i) = addr (s₀.gpr .esp) (4 + 4 * 0) + _
  rw [addr_eq (by omega_arith), addr_eq (by omega_arith), Offset.add_add, show 4 + 4 * 0 + 4 * i = 4 + 4 * i by omega_arith]

theorem IPre.argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd, hp.argAddr_eq hi]
  exact in_rw (r := iargsR s₀) (by simp) (Offset.contains_base _ (by omega_arith) (by omega_arith))

/-- The arguments, unchanged outside the output and the scratch buffer. -/
theorem IPre.arg_eq {m : Mem} (hf : Frame [outR s₀, iscrR s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i := by
  obtain hsub : Region.Sub ⟨argAddr s₀ i, 4⟩ (iargsR s₀) := by
    rw [hp.argAddr_eq hi]; exact Offset.sub_base _ (by omega_arith)
  refine hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.args_out.sub_left hsub
  · exact hp.args_scr.sub_left hsub

/-- The key is unchanged while only the scratch buffer changes. -/
theorem IPre.keyRead {m : Mem} (hf : Frame [iscrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ Kl s₀) :
    m.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨(K s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ hd)) (by decide)

omit hp in
/-- DES key `j` from its two words. -/
theorem kw_eq (j : Nat) :
    bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) j)) 32) ++
      bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) j + 4)) 32) = kw s₀ j := by
  rw [bswap_eq, bswap_eq, byteRev32_append, kw, readW64_split, Offset.add_add]

end

/-! ## The prologue -/

/-- A word of the key, byte-reversed, to the scratch buffer. -/
theorem keyWord_wp {s₀ : State} (hp : IPre s₀) {s : State} {d o : Nat} {rest : List Instr} {Q : State → Prop}
    (hd : d + 4 ≤ Kl s₀) (ho : o + 4 ≤ 640)
    (hcx : s.gpr .ecx = K s₀) (hbp : s.gpr .ebp = Sc s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [iscrR s₀] s₀.mem s.mem)
    (k : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = s.mem.writeW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 o)
        (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 d) 32)) → WP isa (.block rest) s' Q) :
    WP isa (.block (keyWord d o ++ rest)) s Q := by
  show WP isa (.block (.mov .eax (.mem (at_ .ecx d)) :: .bswap .eax :: .store (at_ .ebp o) .eax :: rest)) s Q
  refine wp_movm (hp.keyEa hcx (by omega_arith)) (by rw [hrd, hwr]; exact hp.inKey hd (by decide))
    fun s₁ u₁ => wp_bswap fun s₂ u₂ => ?_
  refine wp_store (hp.scrEa (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hbp]) (by omega_arith))
    (by rw [u₂.wr, u₁.wr, hwr]; exact hp.inScr ho (by decide)) fun s₃ w₃ => k s₃ (fun r hr => ?_)
    (by rw [w₃.rd, u₂.rd, u₁.rd]) (by rw [w₃.wr, u₂.wr, u₁.wr]) ?_
  · rw [w₃.gpr, u₂.other _ hr, u₁.other _ hr]
  · rw [w₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, hp.keyRead hf hd]

/-- A byte offset of the scratch buffer in its bytes `[100, 124)`. -/
theorem keysC {S : Addr} {d : Nat} (h₁ : 100 ≤ d) (h₂ : d + 4 ≤ 124) :
    (⟨S + BitVec.ofNat 64 100, 24⟩ : Region).Contains (S + BitVec.ofNat 64 d) (32 / 8) := by
  rw [show S + BitVec.ofNat 64 d = S + BitVec.ofNat 64 100 + BitVec.ofNat 64 (d - 100) from
    (Offset.add_add_eq _ (by omega_arith)).symm]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem initPre_wp {s₀ : State} (hp : IPre s₀) : WP isa initPre s₀ (KInv s₀ 0) := by
  have sf := hp.scr_fit
  have sf' : (arg s₀ 3).toNat + 640 ≤ 2 ^ 32 := hp.scr_fit
  obtain kl : 16 ≤ Kl s₀ := by rcases hp.valid with h | h <;> omega_arith
  rw [show initPre = .seq (.block (.mov .eax (stk 16) :: (Spill.saveCode .eax saved ++
      (.mov .ebp (.reg .eax) :: .mov .ecx (stk 4) :: (keyWord 0 100 ++ (keyWord 4 104 ++ (keyWord 8 108 ++
        (keyWord 12 112 ++ ([.mov .eax (stk 8), .alu .cmp .eax (.imm 16)] : List Instr)))))))))
      (.seq (.ite .e (.block [.mov .eax (.mem (at_ .ecx 0)), .mov .edx (.mem (at_ .ecx 4))])
          (.block [.mov .eax (.mem (at_ .ecx 16)), .mov .edx (.mem (at_ .ecx 20))]))
        (.block [.bswap .eax, .bswap .edx, .store (at_ .ebp 116) .eax, .store (at_ .ebp 120) .edx,
          .mov .esi (.reg .ebp), .alu .add .esi (.imm 100), .mov .edi (stk 12), .mov .edx (.imm 3)])) from rfl]
  refine WP.seq ?_
  refine wp_arg (s₀ := s₀) 3 rfl rfl (hp.argIn rfl rfl (by decide)) rfl fun s₁ u₁ => ?_
  refine Spill.save_ofNat_ok saved saved_fits (by rw [u₁.gpr]; exact fits_of hp.scr_fit (by decide))
    (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    rw [u₁.gpr, u₁.wr]
    exact hp.inScr (by omega_arith) (by decide)
  obtain hm₂ : s₂.mem = savedMem s₀ (Sc s₀) := by
    rw [u₂.mem, u₁.mem, u₁.gpr, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  obtain sv : Frame [iscrR s₀] s₀.mem (savedMem s₀ (Sc s₀)) := (savedMem_frame s₀ (Sc s₀)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨iscrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  obtain toOS : ∀ {m}, Frame [iscrR s₀] s₀.mem m → Frame [outR s₀, iscrR s₀] s₀.mem m := fun hf =>
    hf.mono (by simp)
  obtain scrC : ∀ d, d + 4 ≤ 640 → (iscrR s₀).Contains ((Sc s₀).setWidth 64 + BitVec.ofNat 64 d) (32 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega_arith)
  refine wp_mov fun s₃ u₃ => ?_
  obtain e₃ : s₃.gpr .ebp = Sc s₀ := by rw [u₃.gpr, u₂.gpr, u₁.gpr]
  obtain esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  refine wp_arg (s₀ := s₀) 0 rfl esp₃ (hp.argIn rd₃ wr₃ (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_eq (toOS sv) (by decide)) fun s₄ u₄ => ?_
  have cx₄ : s₄.gpr .ecx = K s₀ := u₄.gpr
  obtain bp₄ : s₄.gpr .ebp = Sc s₀ := by rw [u₄.other _ (by decide), e₃]
  -- The four words of the first two DES keys.
  refine keyWord_wp hp (by omega_arith) (by decide) cx₄ bp₄ (by rw [u₄.rd, rd₃]) (by rw [u₄.wr, wr₃])
    (by rw [u₄.mem, u₃.mem, hm₂]; exact sv) fun s₅ g₅ rd₅ wr₅ m₅ => ?_
  obtain F₅ : Frame [iscrR s₀] s₀.mem s₅.mem := by
    rw [m₅, u₄.mem, u₃.mem, hm₂]; exact sv.writeW (List.mem_singleton_self _) _ (scrC 100 (by decide))
  refine keyWord_wp hp (by omega_arith) (by decide) (by rw [g₅ _ (by decide), cx₄]) (by rw [g₅ _ (by decide), bp₄])
    (by rw [rd₅, u₄.rd, rd₃]) (by rw [wr₅, u₄.wr, wr₃]) F₅ fun s₆ g₆ rd₆ wr₆ m₆ => ?_
  obtain F₆ : Frame [iscrR s₀] s₀.mem s₆.mem := by
    rw [m₆]; exact F₅.writeW (List.mem_singleton_self _) _ (scrC 104 (by decide))
  refine keyWord_wp hp (by omega_arith) (by decide) (by rw [g₆ _ (by decide), g₅ _ (by decide), cx₄])
    (by rw [g₆ _ (by decide), g₅ _ (by decide), bp₄]) (by rw [rd₆, rd₅, u₄.rd, rd₃])
    (by rw [wr₆, wr₅, u₄.wr, wr₃]) F₆ fun s₇ g₇ rd₇ wr₇ m₇ => ?_
  obtain F₇ : Frame [iscrR s₀] s₀.mem s₇.mem := by
    rw [m₇]; exact F₆.writeW (List.mem_singleton_self _) _ (scrC 108 (by decide))
  refine keyWord_wp hp (by omega_arith) (by decide) (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), cx₄])
    (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), bp₄]) (by rw [rd₇, rd₆, rd₅, u₄.rd, rd₃])
    (by rw [wr₇, wr₆, wr₅, u₄.wr, wr₃]) F₇ fun s₈ g₈ rd₈ wr₈ m₈ => ?_
  obtain F₈ : Frame [iscrR s₀] s₀.mem s₈.mem := by
    rw [m₈]; exact F₇.writeW (List.mem_singleton_self _) _ (scrC 112 (by decide))
  obtain g₈' : ∀ r, r ≠ .eax → s₈.gpr r = s₄.gpr r := fun r h => by rw [g₈ r h, g₇ r h, g₆ r h, g₅ r h]
  obtain rd₈' : s₈.rd = s₀.rd := by rw [rd₈, rd₇, rd₆, rd₅, u₄.rd, rd₃]
  obtain wr₈' : s₈.wr = s₀.wr := by rw [wr₈, wr₇, wr₆, wr₅, u₄.wr, wr₃]
  obtain esp₈ : s₈.gpr .esp = s₀.gpr .esp := by rw [g₈' _ (by decide), u₄.other _ (by decide), esp₃]
  refine wp_arg (s₀ := s₀) 1 rfl esp₈ (hp.argIn rd₈' wr₈' (by decide)) (hp.arg_eq (toOS F₈) (by decide))
    fun s₉ u₉ => wp_cmpi fun s₁₀ f₁₀ _ z₁₀ => WP.block_nil ?_
  obtain ev : isa.eval .e s₁₀ = some (decide (Kl s₀ = 16)) := by
    rw [eval_e', z₁₀, u₉.gpr, show arg s₀ 1 = BitVec.ofNat 32 (Kl s₀) by simp [Kl],
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, MdStream.X86.sub_beq (arg s₀ 1).isLt (by decide)]
  obtain g₁₀ : ∀ r, r ≠ .eax → s₁₀.gpr r = s₄.gpr r := fun r h => by rw [f₁₀.gpr, u₉.other _ h, g₈' r h]
  obtain rd₁₀ : s₁₀.rd = s₀.rd := by rw [f₁₀.rd, u₉.rd, rd₈']
  obtain wr₁₀ : s₁₀.wr = s₀.wr := by rw [f₁₀.wr, u₉.wr, wr₈']
  obtain mem₁₀ : s₁₀.mem = s₈.mem := by rw [f₁₀.mem, u₉.mem]
  -- The third DES key.
  obtain third : ∀ d, d + 8 ≤ Kl s₀ →
      WP isa (.block [.mov .eax (.mem (at_ .ecx d)), .mov .edx (.mem (at_ .ecx (d + 4)))]) s₁₀ fun s₁₁ =>
        s₁₁.gpr .eax = s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 d) 32 ∧
        s₁₁.gpr .edx = s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (d + 4)) 32 ∧
        (∀ r, r ≠ .eax → r ≠ .edx → s₁₁.gpr r = s₁₀.gpr r) ∧ s₁₁.mem = s₈.mem ∧ s₁₁.rd = s₀.rd ∧
        s₁₁.wr = s₀.wr := by
    intro d hd
    obtain cx : s₁₀.gpr .ecx = K s₀ := by rw [g₁₀ _ (by decide), cx₄]
    refine wp_movm (hp.keyEa cx (by omega_arith)) (by rw [rd₁₀, wr₁₀]; exact hp.inKey (by omega_arith) (by decide))
      fun s₁₁ u₁₁ => ?_
    refine wp_movm (hp.keyEa (by rw [u₁₁.other _ (by decide), cx]) (by omega_arith))
      (by rw [u₁₁.rd, u₁₁.wr, rd₁₀, wr₁₀]; exact hp.inKey (by omega_arith) (by decide))
      fun s₁₂ u₁₂ => WP.block_nil ⟨?_, ?_, fun r h4 h5 => ?_, ?_, ?_, ?_⟩
    · rw [u₁₂.other _ (by decide), u₁₁.gpr, mem₁₀, hp.keyRead F₈ (by omega_arith)]
    · rw [u₁₂.gpr, u₁₁.mem, mem₁₀, hp.keyRead F₈ (by omega_arith)]
    · rw [u₁₂.other _ h5, u₁₁.other _ h4]
    · rw [u₁₂.mem, u₁₁.mem, mem₁₀]
    · rw [u₁₂.rd, u₁₁.rd, rd₁₀]
    · rw [u₁₂.wr, u₁₁.wr, wr₁₀]
  refine WP.seq (WP.mono (Q := fun (s₁₁ : State) =>
      s₁₁.gpr .eax = s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) 2)) 32 ∧
      s₁₁.gpr .edx = s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) 2 + 4)) 32 ∧
      (∀ r, r ≠ .eax → r ≠ .edx → s₁₁.gpr r = s₁₀.gpr r) ∧ s₁₁.mem = s₈.mem ∧ s₁₁.rd = s₀.rd ∧
      s₁₁.wr = s₀.wr) ?_ fun s₁₁ h₁₁ => ?_)
  · by_cases h16 : Kl s₀ = 16
    · refine WP.ite true (by rw [ev]; simp [h16]) (fun _ => ?_) (fun h => by cases h)
      have := third 0 (by omega_arith)
      rwa [show keyOff (Kl s₀) 2 = 0 by simp [keyOff, h16]]
    · refine WP.ite false (by rw [ev]; simp [h16]) (fun h => by cases h) (fun _ => ?_)
      obtain h24 : Kl s₀ = 24 := by rcases hp.valid with h | h <;> omega_arith
      have := third 16 (by omega_arith)
      rwa [show keyOff (Kl s₀) 2 = 16 by simp [keyOff, h24]]
  obtain ⟨ax₁₁, dx₁₁, g₁₁, m₁₁, rd₁₁, wr₁₁⟩ := h₁₁
  obtain bp₁₁ : s₁₁.gpr .ebp = Sc s₀ := by rw [g₁₁ _ (by decide) (by decide), g₁₀ _ (by decide), bp₄]
  refine wp_bswap fun s₁₂ u₁₂ => wp_bswap fun s₁₃ u₁₃ => ?_
  obtain bp₁₃ : s₁₃.gpr .ebp = Sc s₀ := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), bp₁₁]
  refine wp_store (hp.scrEa bp₁₃ (by decide)) (by rw [u₁₃.wr, u₁₂.wr, wr₁₁]; exact hp.inScr (by decide) (by decide))
    fun s₁₄ w₁₄ => ?_
  refine wp_store (hp.scrEa (by rw [w₁₄.gpr, bp₁₃]) (by decide))
    (by rw [w₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁]; exact hp.inScr (by decide) (by decide)) fun s₁₅ w₁₅ => ?_
  refine wp_mov fun s₁₆ u₁₆ => wp_addi fun s₁₇ u₁₇ => ?_
  obtain esp₁₇ : s₁₇.gpr .esp = s₀.gpr .esp := by
    rw [u₁₇.other _ (by decide), u₁₆.other _ (by decide), w₁₅.gpr, w₁₄.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), g₁₁ _ (by decide) (by decide), g₁₀ _ (by decide), u₄.other _ (by decide), esp₃]
  obtain rd₁₇ : s₁₇.rd = s₀.rd := by rw [u₁₇.rd, u₁₆.rd, w₁₅.rd, w₁₄.rd, u₁₃.rd, u₁₂.rd, rd₁₁]
  obtain wr₁₇ : s₁₇.wr = s₀.wr := by rw [u₁₇.wr, u₁₆.wr, w₁₅.wr, w₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁]
  obtain mem₁₅ : s₁₅.mem = ((((((savedMem s₀ (Sc s₀)).writeW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 100)
      (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 0) 32))).writeW
      ((Sc s₀).setWidth 64 + BitVec.ofNat 64 104) (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 4) 32))).writeW
      ((Sc s₀).setWidth 64 + BitVec.ofNat 64 108) (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 8) 32))).writeW
      ((Sc s₀).setWidth 64 + BitVec.ofNat 64 112)
        (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 12) 32))).writeW
      ((Sc s₀).setWidth 64 + BitVec.ofNat 64 116)
        (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) 2)) 32))).writeW
      ((Sc s₀).setWidth 64 + BitVec.ofNat 64 120)
        (bswap (s₀.mem.readW ((K s₀).setWidth 64 + BitVec.ofNat 64 (keyOff (Kl s₀) 2 + 4)) 32)) := by
    rw [w₁₅.mem, w₁₄.mem, w₁₄.gpr, u₁₃.gpr, u₁₃.other .eax (by decide), u₁₂.gpr, u₁₃.mem, u₁₂.mem,
      u₁₂.other .edx (by decide), ax₁₁, dx₁₁, m₁₁, m₈, m₇, m₆, m₅, u₄.mem, u₃.mem, hm₂]
  refine wp_arg (s₀ := s₀) 2 rfl esp₁₇ (hp.argIn rd₁₇ wr₁₇ (by decide))
    (by
      rw [u₁₇.mem, u₁₆.mem, mem₁₅]
      refine hp.arg_eq (toOS ?_) (by decide)
      exact (((((sv.writeW (List.mem_singleton_self _) _ (scrC 100 (by decide))).writeW (List.mem_singleton_self _) _
        (scrC 104 (by decide))).writeW (List.mem_singleton_self _) _ (scrC 108 (by decide))).writeW
        (List.mem_singleton_self _) _ (scrC 112 (by decide))).writeW (List.mem_singleton_self _) _
        (scrC 116 (by decide))).writeW (List.mem_singleton_self _) _ (scrC 120 (by decide)))
    fun s₁₈ u₁₈ => wp_movi fun s₁₉ u₁₉ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => absurd hn (by omega_arith), ?_⟩
  · rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.other _ (by decide),
      w₁₅.gpr, w₁₄.gpr, bp₁₃]
  · rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.gpr, w₁₅.gpr, w₁₄.gpr, bp₁₃]; rfl
  · rw [u₁₉.other _ (by decide), u₁₈.gpr, add_zero32]
  · rw [u₁₉.gpr]; rfl
  · rw [u₁₉.other _ (by decide), u₁₈.other _ (by decide), esp₁₇]
  · rw [u₁₉.rd, u₁₈.rd, rd₁₇]
  · rw [u₁₉.wr, u₁₈.wr, wr₁₇]
  · rw [u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, mem₁₅, ← kw_eq (s₀ := s₀) j]
    rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [show keyOff (Kl s₀) 0 = 0 by simp [keyOff]]
      simp (disch := decide) only [readW_writeW_far, Mem.readW_writeW_self32]
    · rw [show keyOff (Kl s₀) 1 = 8 by simp [keyOff]]
      simp (disch := decide) only [readW_writeW_far, Mem.readW_writeW_self32]
    · simp (disch := decide) only [readW_writeW_far, Mem.readW_writeW_self32]
  · rw [u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, mem₁₅]
    obtain c : ∀ d, 100 ≤ d → d + 4 ≤ 124 → (⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 100, 24⟩ : Region).Contains
        ((Sc s₀).setWidth 64 + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ => keysC h₁ h₂
    exact ((((((Frame.refl _ _).writeW (by simp) _ (c 100 (by decide) (by decide))).writeW (by simp) _
      (c 104 (by decide) (by decide))).writeW (by simp) _ (c 108 (by decide) (by decide))).writeW (by simp) _
      (c 112 (by decide) (by decide))).writeW (by simp) _ (c 116 (by decide) (by decide))).writeW (by simp) _
      (c 120 (by decide) (by decide))

/-! ## The round keys -/

theorem keyStep_ok {s₀ : State} (hp : IPre s₀) {i : Nat} (hi : i < 3) {s : State} (h : KInv s₀ i s) :
    WP isa (.block keysBody) s fun s' => KInv s₀ (i + 1) s' ∧ s'.zf = some (decide (3 - (i + 1) = 0)) := by
  have sf := hp.scr_fit
  have of := hp.out_fit
  obtain oN : (O s₀ + BitVec.ofNat 32 (128 * i)).toNat = (O s₀).toNat + 128 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  obtain hok : Straight.Ok kCfg s := by
    refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, fun k hk j hj => ?_⟩
    · simp only [kCfg] at hk
      rw [show kCfg.base = .edi from rfl, h.edi, h.wr, hp.wr]
      exact in_rw (r := outR s₀) (by simp) (contains_w_off (by omega_arith) (by omega_arith))
    · simp only [kCfg] at hk
      rw [show kCfg.ext = .esi from rfl, h.esi, h.rd, h.wr, hp.rd, hp.wr]
      exact in_rw (r := iscrR s₀) (by simp) (contains_w_off (by omega_arith) (by omega_arith))
    · show (s.gpr .edi).toNat + 4 * 32 ≤ 2 ^ 32
      rw [h.edi, oN]; omega_arith
    · simp only [kCfg] at hk hj
      rw [show kCfg.base = .edi from rfl, show kCfg.ext = .esi from rfl, h.edi, h.esi]
      exact hp.out_scr.sep (contains_w_off (by omega_arith) (by omega_arith)) (contains_w_off (by omega_arith) (by omega_arith))
  obtain ⟨s₁, run₁, rk₁, hi₁, rd₁, wr₁, k₁, f₁⟩ := roundKeys_ok hok
  rw [keysBody, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  refine wp_addi fun s₂ u₂ => wp_addi fun s₃ u₃ => wp_subi fun s₄ u₄ z₄ => WP.block_nil ?_
  have kk : ∀ r ∈ kKept, s₁.gpr r = s.gpr r := k₁
  obtain dk : desKey s = kw s₀ i := by
    rw [desKey, h.esi, wordAddr_off _ (by omega_arith), wordAddr_off _ (by omega_arith), show 100 + 8 * i + 4 * 0 = 100 + 8 * i by omega_arith,
      show 100 + 8 * i + 4 * 1 = 104 + 8 * i by omega_arith, h.keys i hi]
  obtain slotR : Straight.slotRegion kCfg s = ⟨(O s₀).setWidth 64 + BitVec.ofNat 64 (128 * i), 128⟩ := by
    simp only [Straight.slotRegion]; rw [show kCfg.base = .edi from rfl, h.edi, ← addr_zero, addr_off2 (by omega_arith), add0]; rfl
  rw [slotR] at f₁
  obtain m₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  obtain dx₁ : s₁.gpr .edx = BitVec.ofNat 32 (3 - i) := by rw [kk _ (by simp [kKept]), h.edx]
  obtain dec : BitVec.ofNat 32 (3 - i) - 1 = BitVec.ofNat 32 (3 - (i + 1)) := by
    rw [ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  obtain wA : ∀ k < 32, wordAddr (s.gpr .edi) k = (O s₀).setWidth 64 + BitVec.ofNat 64 (128 * i + 4 * k) :=
    fun k hk => by rw [h.edi, wordAddr_off _ (by omega_arith)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => ?_, ?_⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), kk _ (by simp [kKept]), h.ebp]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), kk _ (by simp [kKept]), h.esi,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, Offset.add_add, show 100 + 8 * i + 8 = 100 + 8 * (i + 1) by omega_arith]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, kk _ (by simp [kKept]), h.edi,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, Offset.add_add, show 128 * i + 128 = 128 * (i + 1) by omega_arith]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), dx₁, dec]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), kk _ (by simp [kKept]), h.esp]
  · rw [u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  · rw [m₄, ← h.keys j hj]
    obtain keep : ∀ d, 100 ≤ d → d + 4 ≤ 124 → s₁.mem.readW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 =
        s.mem.readW ((Sc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 := fun d h₁ h₂ =>
      f₁.readW (r := ⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.out_scr.sub_left (Offset.sub_base _ (by omega_arith))).symm.sub_left (Offset.sub_base _ (by omega_arith)))
        (by decide)
    rw [keep _ (by omega_arith) (by omega_arith), keep _ (by omega_arith) (by omega_arith)]
  · rw [m₄]
    by_cases hn' : n < 16 * i
    · rw [← h.sched n hn', f₁.readW (r := ⟨(O s₀).setWidth 64 + BitVec.ofNat 64 (8 * n), 8⟩)
        (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    · obtain ⟨j, rfl⟩ : ∃ j, n = 16 * i + j := ⟨n - 16 * i, by omega_arith⟩
      obtain hj : j < 16 := by omega_arith
      obtain hk := keyOff_le hp hi
      rw [readW64_split, Offset.add_add, show 8 * (16 * i + j) + 4 = 128 * i + 4 * (2 * j + 1) by omega_arith,
        ← wA (2 * j + 1) (by omega_arith), show 8 * (16 * i + j) = 128 * i + 4 * (2 * j) by omega_arith, ← wA (2 * j) (by omega_arith),
        append_of_hi _ _ (hi₁ j hj), rk₁ j hj, dk, kw, expandKey_getD _ hi hj, Proof.Cmac.bytesAt_length,
        decode_bytesAt _ _ hk]
  · rw [m₄]
    exact h.frame.trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨(O s₀).setWidth 64, 384⟩, by simp, Offset.sub_base _ (by omega_arith)⟩)
  · rw [z₄, u₃.other _ (by decide), u₂.other _ (by decide), dx₁, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      MdStream.X86.sub_beq (by omega_arith) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

theorem keys_ok {s₀ : State} (hp : IPre s₀) {s : State} (h : KInv s₀ 0 s) :
    WP isa (.loop (.block keysBody) .ne) s (KInv s₀ 3) := by
  refine WP.loop (M := isa) (body := .block keysBody) (c := .ne) (Q := KInv s₀ 3)
    (fun (n : Nat) (t : State) => ∃ i, n = 3 - i ∧ i < 3 ∧ KInv s₀ i t) ?_ 3 s ⟨0, rfl, by decide, h⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (keyStep_ok hp hi ht) fun t' ⟨h', z'⟩ => ?_
  by_cases hz : i + 1 = 3
  · left
    refine ⟨by rw [eval_ne', z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [eval_ne', z']; simp; omega_arith, 3 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, h'⟩

/-! ## The subkeys -/

/-- `dbl d` doubles `eax:edx` and stores it, as bytes, at `[edi + d]`. -/
theorem dbl_wp {s : State} {d : Nat} {a : Addr} {rest : List Instr} {Q : State → Prop}
    (ha : addr (s.gpr .edi) d = a) (ha4 : addr (s.gpr .edi) (d + 4) = a + BitVec.ofNat 64 4)
    (w0 : InRegions s.wr a 4) (w4 : InRegions s.wr (a + BitVec.ofNat 64 4) 4)
    (k : ∀ s', s'.gpr .eax ++ s'.gpr .edx = dbl64 (s.gpr .eax ++ s.gpr .edx) →
      s'.mem = (s.mem.writeW a (bswap (s'.gpr .eax))).writeW (a + BitVec.ofNat 64 4) (bswap (s'.gpr .edx)) →
      (∀ r, r ∉ [Reg.eax, .ebx, .ecx, .edx] → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Q) :
    WP isa (.block (dbl d ++ rest)) s Q := by
  show WP isa (.block (.mov .ecx (.reg .eax) :: .shift .shr .ecx 31 :: .mov .ebx (.imm 0) ::
    .alu .sub .ebx (.reg .ecx) :: .alu .and .ebx (.imm 0x1b) :: .mov .ecx (.reg .edx) :: .shift .shr .ecx 31 ::
    .alu .add .eax (.reg .eax) :: .alu .or .eax (.reg .ecx) :: .alu .add .edx (.reg .edx) ::
    .alu .xor .edx (.reg .ebx) :: .mov .ecx (.reg .eax) :: .bswap .ecx :: .store (at_ .edi d) .ecx ::
    .mov .ecx (.reg .edx) :: .bswap .ecx :: .store (at_ .edi (d + 4)) .ecx :: rest)) s Q
  refine wp_mov fun s₁ u₁ => wp_shr (by decide) fun s₂ u₂ => wp_movi fun s₃ u₃ => wp_sub fun s₄ u₄ _ =>
    wp_andi fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_shr (by decide) fun s₇ u₇ => wp_add fun s₈ u₈ =>
    wp_or fun s₉ u₉ => wp_add fun s₁₀ u₁₀ => wp_xorr fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ => wp_bswap fun s₁₃ u₁₃ => ?_
  obtain g₁₃ : ∀ r, r ∉ [Reg.eax, .ebx, .ecx, .edx] → s₁₃.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₃.other _ hr.2.2.1, u₁₂.other _ hr.2.2.1, u₁₁.other _ hr.2.2.2, u₁₀.other _ hr.2.2.2, u₉.other _ hr.1,
      u₈.other _ hr.1, u₇.other _ hr.2.2.1, u₆.other _ hr.2.2.1, u₅.other _ hr.2.1, u₄.other _ hr.2.1,
      u₃.other _ hr.2.1, u₂.other _ hr.2.2.1, u₁.other _ hr.2.2.1]
  obtain m₁₃ : s₁₃.mem = s.mem := by
    rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain wr₁₃ : s₁₃.wr = s.wr := by
    rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain di₁₃ : s₁₃.gpr .edi = s.gpr .edi := g₁₃ _ (by decide)
  refine wp_store (by rw [ea_at', di₁₃, ha]) (by rw [wr₁₃]; exact w0) fun s₁₄ w₁₄ => ?_
  refine wp_mov fun s₁₅ u₁₅ => wp_bswap fun s₁₆ u₁₆ => ?_
  refine wp_store (by rw [ea_at', u₁₆.other _ (by decide), u₁₅.other _ (by decide), w₁₄.gpr, di₁₃, ha4])
    (by rw [u₁₆.wr, u₁₅.wr, w₁₄.wr, wr₁₃]; exact w4) fun s₁₇ w₁₇ => ?_
  obtain r0f : s₁₇.gpr .eax = s₁₁.gpr .eax := by
    rw [w₁₇.gpr, u₁₆.other _ (by decide), u₁₅.other _ (by decide), w₁₄.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide)]
  obtain r1f : s₁₇.gpr .edx = s₁₁.gpr .edx := by
    rw [w₁₇.gpr, u₁₆.other _ (by decide), u₁₅.other _ (by decide), w₁₄.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide)]
  refine k s₁₇ ?_ ?_ (fun r hr => ?_) ?_ ?_
  · have a3 : s₁₀.gpr .ebx = ((0 : BitVec 32) - (s.gpr .eax >>> 31)) &&& (0x1b : BitVec 32) := by
      rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr]
    obtain a0 : s₁₁.gpr .eax = s.gpr .eax <<< 1 ||| s.gpr .edx >>> 31 := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₈.other _ (by decide), u₇.gpr,
        u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide), add_self]
    obtain a1 : s₁₁.gpr .edx =
        s.gpr .edx <<< 1 ^^^ (((0 : BitVec 32) - (s.gpr .eax >>> 31)) &&& (0x1b : BitVec 32)) := by
      rw [u₁₁.gpr, a3, u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), add_self]
    rw [r0f, r1f, a0, a1, dbl_append]
  · rw [w₁₇.mem, u₁₆.mem, u₁₅.mem, w₁₄.mem, m₁₃, u₁₆.gpr, u₁₅.gpr, w₁₄.gpr, u₁₃.other .edx (by decide),
      u₁₃.gpr, u₁₂.gpr, r0f, r1f, u₁₂.other .edx (by decide)]
  · rw [w₁₇.gpr, u₁₆.other _ (by simp_all), u₁₅.other _ (by simp_all), w₁₄.gpr, g₁₃ r hr]
  · rw [w₁₇.rd, u₁₆.rd, u₁₅.rd, w₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd,
      u₃.rd, u₂.rd, u₁.rd]
  · rw [w₁₇.wr, u₁₆.wr, u₁₅.wr, w₁₄.wr, wr₁₃]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initX86.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initX86.post s₀ s' := by
  obtain hp := IPre.of h0
  have sf := hp.scr_fit
  have of := hp.out_fit
  have of' : (arg s₀ 2).toNat + 400 ≤ 2 ^ 32 := hp.out_fit
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (keys_ok hp h₁) fun s₂ h₂ => ?_)
  obtain F₂ : Frame [outR s₀, iscrR s₀] s₀.mem s₂.mem :=
    ((savedMem_frame s₀ (Sc s₀)).sub fun r hr => ⟨iscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩).trans
    (h₂.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨iscrR s₀, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨outR s₀, by simp, Region.sub_prefix (by decide)⟩)
  -- The key schedule is in place.
  obtain hsch₂ : Spec.TripleDes.scheduleAt s₂.mem ((O s₀).setWidth 64) = Spec.TripleDes.expandKey (keyB s₀) := by
    apply Vector.ext
    intro n hn
    rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, h₂.sched n (by omega_arith)]
  refine WP.seq ?_
  simp only [stk]
  refine wp_arg (s₀ := s₀) 2 rfl h₂.esp (hp.argIn h₂.rd h₂.wr (by decide)) (hp.arg_eq F₂ (by decide))
    fun s₃ u₃ => wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => WP.block_nil ?_
  obtain g₅ : ∀ r, r ∉ [Reg.eax, .edx, .esi] → s₅.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.1, u₄.other _ hr.1, u₃.other _ hr.2.2]
  obtain esi₅ : s₅.gpr .esi = O s₀ := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  obtain ebp₅ : s₅.gpr .ebp = Sc s₀ := by rw [g₅ _ (by decide), h₂.ebp]
  obtain ax₅ : s₅.gpr .eax ++ s₅.gpr .edx = (0 : BitVec 64) := by rw [u₅.gpr, u₅.other _ (by decide), u₄.gpr]; rfl
  obtain m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  obtain rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, h₂.rd]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, h₂.wr]
  obtain hsch₅ : sch s₅ = Spec.TripleDes.expandKey (keyB s₀) := by
    show Spec.TripleDes.scheduleAt s₅.mem ((s₅.gpr .esi).setWidth 64) = _
    rw [esi₅, m₅, hsch₂]
  obtain bp : BlockPre s₅ :=
    { sched := ⟨400, by rw [esi₅, rd₅, wr₅, hp.rd, hp.wr]; simp, by decide, by rw [esi₅]; exact of⟩
      scr := ⟨640, by rw [ebp₅, wr₅, hp.wr]; simp, by decide, by rw [ebp₅]; exact sf⟩
      disj := by
        rw [esi₅, ebp₅]
        exact (hp.out_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₆ ⟨same₆, esi₆, ax₆⟩ => ?_)
  rw [ax₅, hsch₅] at ax₆
  obtain xR₅ : xR s₅ = ⟨(Sc s₀).setWidth 64, 84⟩ := by rw [xR, ebp₅]
  obtain f₆ : Frame [⟨(Sc s₀).setWidth 64, 84⟩] s₂.mem s₆.mem := by rw [← m₅, ← xR₅]; exact same₆.frame
  obtain F₆ : Frame [outR s₀, iscrR s₀] s₀.mem s₆.mem :=
    F₂.trans (f₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨iscrR s₀, by simp, Region.sub_prefix (by decide)⟩)
  obtain esp₆ : s₆.gpr .esp = s₀.gpr .esp := by rw [same₆.esp, g₅ _ (by decide), h₂.esp]
  obtain ebp₆ : s₆.gpr .ebp = Sc s₀ := by rw [same₆.ebp, ebp₅]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [same₆.rd, rd₅]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [same₆.wr, wr₅]
  show WP isa (.block (.mov .edi (stk 12) :: .alu .add .edi (.imm 384) :: (dbl 0 ++ (dbl 8 ++ restore)))) s₆ _
  refine wp_arg (s₀ := s₀) 2 rfl esp₆ (hp.argIn rd₆ wr₆ (by decide)) (hp.arg_eq F₆ (by decide))
    fun s₇ u₇ => wp_addi fun s₈ u₈ => ?_
  obtain di₈ : s₈.gpr .edi = O s₀ + 384 := by rw [u₈.gpr, u₇.gpr]
  obtain oA : ∀ d, d < 16 → addr (s₈.gpr .edi) d = (O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d) := fun d hd => by
    rw [di₈, show (384 : BitVec 32) = BitVec.ofNat 32 384 from rfl, addr_off2 (by omega_arith), Offset.add_add]
  obtain wO : ∀ d, d + 4 ≤ 16 → InRegions s₈.wr ((O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d)) 4 := fun d hd => by
    rw [u₈.wr, u₇.wr, wr₆]; exact hp.inOut (by omega_arith) (by decide)
  obtain a4 : ∀ d, (O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d) + BitVec.ofNat 64 4 =
      (O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d + 4) := fun d => Offset.add_add _ _ _
  refine dbl_wp (a := (O s₀).setWidth 64 + BitVec.ofNat 64 (384 + 0)) (oA 0 (by decide))
    (by rw [oA 4 (by decide), a4]) (wO 0 (by decide)) (by rw [a4]; exact wO 4 (by decide))
    fun s₉ ax₉ m₉ g₉ rd₉ wr₉ => ?_
  refine dbl_wp (a := (O s₀).setWidth 64 + BitVec.ofNat 64 (384 + 8)) (by rw [g₉ _ (by decide), oA 8 (by decide)])
    (by rw [g₉ _ (by decide), oA 12 (by decide), a4]) (by rw [wr₉]; exact wO 8 (by decide))
    (by rw [wr₉, a4]; exact wO 12 (by decide)) fun s₁₀ ax₁₀ m₁₀ g₁₀ rd₁₀ wr₁₀ => ?_
  obtain ebp₁₀ : s₁₀.gpr .ebp = Sc s₀ := by
    rw [g₁₀ _ (by decide), g₉ _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), ebp₆]
  obtain rdwr₁₀ : s₁₀.rd ++ s₁₀.wr = [ikeyR s₀, iargsR s₀, outR s₀, iscrR s₀] := by
    rw [rd₁₀, wr₁₀, rd₉, wr₉, u₈.rd, u₈.wr, u₇.rd, u₇.wr, rd₆, wr₆, hp.rd, hp.wr]; rfl
  -- What changed since the registers were saved.
  obtain oC : ∀ d, d + 4 ≤ 16 → (outR s₀).Contains ((O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d)) (32 / 8) :=
    fun d hd => Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain F₁₀ : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₁₀.mem := by
    obtain F₂' : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₂.mem := h₂.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 100, 24⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨outR s₀, by simp, Region.sub_prefix (by decide)⟩
    obtain F₆' : Frame (ichg s₀) (savedMem s₀ (Sc s₀)) s₆.mem := F₂'.trans (f₆.mono fun r hr => by simp at hr; simp [hr])
    rw [m₁₀, m₉, u₈.mem, u₇.mem, a4, a4]
    exact (((F₆'.writeW (by simp) _ (oC 0 (by decide))).writeW (by simp) _ (oC 4 (by decide))).writeW (by simp) _
      (oC 8 (by decide))).writeW (by simp) _ (oC 12 (by decide))
  refine WP.mono (restore_ok ebp₁₀ (by omega_arith) (fun d h₁' h₂' => by
      rw [rdwr₁₀]; exact in_rw (r := iscrR s₀) (by simp) (Offset.contains_base _ (by omega_arith) (by omega_arith)))
      (saved_of (S := Sc s₀) fun d h₁' h₂' => ?_))
    fun s' r' => ⟨restored r' ?_ ?_, ?_, ?_⟩
  · refine F₁₀.readW (r := ⟨(Sc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (hp.out_scr.sub_right (Offset.sub_base _ (by omega_arith))).symm
  · rw [g₁₀ _ (by decide), g₉ _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), esp₆]
  · rw [r'.mem, F₁₀.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact (savedMem_frame s₀ (Sc s₀)).readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))
      · exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))
      · exact hp.ret_out
  -- The key schedule.
  · show Spec.TripleDes.scheduleAt s'.mem ((O s₀).setWidth 64) = Spec.TripleDes.expandKey (keyB s₀)
    rw [r'.mem, ← hsch₂]
    refine scheduleAt_frame (rs := [iscrR s₀, ⟨(O s₀).setWidth 64 + BitVec.ofNat 64 384, 16⟩]) ?_ fun r hr => ?_
    · have c : ∀ d, d + 4 ≤ 16 → (⟨(O s₀).setWidth 64 + BitVec.ofNat 64 384, 16⟩ : Region).Contains
          ((O s₀).setWidth 64 + BitVec.ofNat 64 (384 + d)) (32 / 8) := fun d hd => by
        rw [← Offset.add_add]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
      rw [m₁₀, m₉, u₈.mem, u₇.mem, a4, a4]
      exact ((((f₆.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨iscrR s₀, by simp, Region.sub_prefix (by decide)⟩).writeW (by simp) _ (c 0 (by decide))).writeW
        (by simp) _ (c 4 (by decide))).writeW (by simp) _ (c 8 (by decide))).writeW (by simp) _ (c 12 (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.out_scr.sub_left (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint _ (by decide) (by omega_arith)
  -- The subkeys.
  · show Spec.Aes.bytesAt s'.mem ((O s₀).setWidth 64 + BitVec.ofNat 64 384) 16 =
      (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (keyB s₀))) 8).1 ++
        (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (keyB s₀))) 8).2
    rw [subkeys_tdes, r'.mem, bytesAt_split, ← le8_readW, ← le8_readW, readW64_split, readW64_split, m₁₀, m₉, u₈.mem,
      u₇.mem]
    simp (disch := decide) only [Offset.add_add, readW_writeW_far, Mem.readW_writeW_self32]
    rw [bswap_eq, bswap_eq, bswap_eq, bswap_eq, byteRev32_append, byteRev32_append, ax₁₀, ax₉,
      u₈.other .eax (by decide), u₈.other .edx (by decide), u₇.other .eax (by decide), u₇.other .edx (by decide), ax₆]

end VG.Proof.CmacTripleDes.X86

end

end

/-!
# TDEA-CMAC on x86: constant time

Untrusted: everything here is checked by Lean. The taint analysis
(`Framework/X86/Taint.lean`) checks that only the stack arguments, which are
public, decide branches and addresses. The functions keep their pointers
and counts in the scratch buffer, the second writable region: the analysis
knows the stack argument holding it is that region's base, so `ebp`, loaded
from it, addresses public words there, and the block's counters and step
are stored and loaded through it.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86

/-- `init`'s initial taint: the stack arguments are public; `out` and
`scratch` are the bases of the writable regions. -/
def initTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [400, 640], argLen := 20, argBases := [(12, 0), (16, 1)] }

/-- `update`'s and `finalize`'s: the stack arguments are public; `state` and
`scratch` are the bases of the writable regions. -/
def streamTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [8, 640], argLen := 24, argBases := [(8, 0), (20, 1)] }

theorem argMem_eq {s₁ s₂ : State} {n : Nat} (f₁ : (s₁.gpr .esp).toNat + n ≤ 2 ^ 32)
    (f₂ : (s₂.gpr .esp).toNat + n ≤ 2 ^ 32) (ha : ∀ i, 4 + 4 * i < n → arg s₁ i = arg s₂ i) {k : Nat}
    (h4 : 4 ≤ k) (hk : k < n) :
    s₁.mem (VG.X86.Taint.argByte s₁ (VG.X86.Taint.depth ([] : List (Option Nat)) + k)) =
      s₂.mem (VG.X86.Taint.argByte s₂ (VG.X86.Taint.depth ([] : List (Option Nat)) + k)) := by
  rw [show VG.X86.Taint.depth ([] : List (Option Nat)) = 0 from rfl, Nat.zero_add,
    VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
    Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
  exact congrArg _ (ha _ (by omega_using [h4, hk]))

/-! ## `init` -/

theorem init_wf {s : State} (h : initX86.pre s) : VG.X86.Taint.Wf initTaint s := by
  have hp := IPre.of h
  have := hp.out_fit; have := hp.scr_fit; have := hp.esp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, initTaint], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [initTaint]; omega_using [this], ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.out_scr
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [this]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [this]) hp.ret_scr hp.args_scr
  · intro p hp'
    simp only [initTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp [initTaint], ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem init_ct : ConstantTime isa initX86.pre initX86.pub init := by
  refine VG.Taint.constantTime (A := taint) initTaint ?_ (by taint_decide)
  intro s₁ s₂ h₁ h₂ ⟨hesp, ha⟩
  have hp₁ := IPre.of h₁; have hp₂ := IPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, init_wf h₁, init_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => argMem_eq (n := 20) hp₁.esp_fit hp₂.esp_fit (fun i hi => ha i (by omega_using [hi])) h4 hk⟩
  · simp only [initTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [outR, iscrR, O, Sc, ha 2 (by omega_using []), ha 3 (by omega_using [])]

/-! ## `update` and `finalize` -/

/-- The state and the scratch buffer, the writable regions of `update` and
`finalize`, from their stack arguments. -/
abbrev streamWr (s : State) : List Region := [⟨(arg s 1).setWidth 64, 8⟩, ⟨(arg s 4).setWidth 64, 640⟩]

theorem streamTaint_wf {s : State} (hwr : s.wr = streamWr s)
    (st_scr : Region.Disjoint ⟨(arg s 1).setWidth 64, 8⟩ ⟨(arg s 4).setWidth 64, 640⟩)
    (ret_st : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 1).setWidth 64, 8⟩)
    (ret_scr : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 4).setWidth 64, 640⟩)
    (args_st : Region.Disjoint ⟨argAddr s 0, 20⟩ ⟨(arg s 1).setWidth 64, 8⟩)
    (args_scr : Region.Disjoint ⟨argAddr s 0, 20⟩ ⟨(arg s 4).setWidth 64, 640⟩)
    (st_fit : (arg s 1).toNat + 8 ≤ 2 ^ 32) (scr_fit : (arg s 4).toNat + 640 ≤ 2 ^ 32)
    (esp_fit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) : VG.X86.Taint.Wf streamTaint s := by
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hwr, streamTaint], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [streamTaint]; omega_using [esp_fit], ?_⟩, ?_⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact st_scr
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [esp_fit]) ret_st args_st
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [esp_fit]) ret_scr args_scr
  · intro p hp'
    simp only [streamTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp [streamTaint], ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

/-- Two runs agree on `streamTaint` when they agree on the stack arguments. -/
theorem streamTaint_agree {s₁ s₂ : State} (w₁ : VG.X86.Taint.Wf streamTaint s₁)
    (w₂ : VG.X86.Taint.Wf streamTaint s₂) (hw₁ : s₁.wr = streamWr s₁) (hw₂ : s₂.wr = streamWr s₂)
    (f₁ : (s₁.gpr .esp).toNat + 24 ≤ 2 ^ 32) (f₂ : (s₂.gpr .esp).toNat + 24 ≤ 2 ^ 32)
    (hesp : s₁.gpr .esp = s₂.gpr .esp) (ha : ∀ i < 5, arg s₁ i = arg s₂ i) :
    VG.X86.Taint.Agree streamTaint s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, w₁, w₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => argMem_eq (n := 24) f₁ f₂ (fun i hi => ha i (by omega_using [hi])) h4 hk⟩
  · simp only [streamTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hw₁, hw₂]; simp only [streamWr, ha 1 (by omega_using []), ha 4 (by omega_using [])]

theorem update_ct : ConstantTime isa updateX86.pre updateX86.pub update := by
  refine VG.Taint.constantTime (A := taint) streamTaint ?_ (by taint_decide)
  intro s₁ s₂ h₁ h₂ ⟨hesp, ha⟩
  have p₁ := UPre.of h₁; have p₂ := UPre.of h₂
  exact streamTaint_agree
    (streamTaint_wf p₁.wr p₁.st_scr p₁.ret_st p₁.ret_scr p₁.args_st p₁.args_scr p₁.st_fit p₁.scr_fit p₁.esp_fit)
    (streamTaint_wf p₂.wr p₂.st_scr p₂.ret_st p₂.ret_scr p₂.args_st p₂.args_scr p₂.st_fit p₂.scr_fit p₂.esp_fit)
    p₁.wr p₂.wr p₁.esp_fit p₂.esp_fit hesp ha

theorem finalize_ct : ConstantTime isa finalizeX86.pre finalizeX86.pub finalize := by
  refine VG.Taint.constantTime (A := taint) streamTaint ?_ (by taint_decide)
  intro s₁ s₂ h₁ h₂ ⟨hesp, ha⟩
  have p₁ := FPre.of h₁; have p₂ := FPre.of h₂
  exact streamTaint_agree
    (streamTaint_wf p₁.wr p₁.st_scr p₁.ret_st p₁.ret_scr p₁.args_st p₁.args_scr p₁.st_fit p₁.scr_fit p₁.esp_fit)
    (streamTaint_wf p₂.wr p₂.st_scr p₂.ret_st p₂.ret_scr p₂.args_st p₂.args_scr p₂.st_fit p₂.scr_fit p₂.esp_fit)
    p₁.wr p₂.wr p₁.esp_fit p₂.esp_fit hesp ha

end VG.Proof.CmacTripleDes.X86

end

end

/-! ### `CmacTripleDes.X86.FinalizeCorrect`, which only this module used -/

section

/-!
# TDEA-CMAC on x86: `vg_cmac_triple_des_finalize` is correct

Untrusted: everything here is checked by Lean. After the branch on the
length, `eax:edx` holds `Mₙ` (`BPost`); the function XORs in the chaining
value `C`, encrypts it and stores `CIPH_K(C ⊕ Mₙ)` as the state, the MAC
(`macFull_split8`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86 VG.Proof.CmacTripleDes VG.Proof.Cmac
open VG.Proof.MdStream.X86 (Upd Mupd wp_movm wp_store wp_bswap)

theorem finalize_wp {s₀ : State} (h0 : finalizeX86.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeX86.post s₀ s' := by
  obtain hp := FPre.of h0
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have tf := hp.st_fit
  have tf' : (arg s₀ 1).toNat + 8 ≤ 2 ^ 32 := hp.st_fit
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  obtain rdwr₁ : s₁.rd ++ s₁.wr = [keyR s₀, lastR s₀, argsR s₀, fstR s₀, fscrR s₀] := by
    rw [h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  obtain stIn : ∀ d, d + 4 ≤ 8 → InRegions (s₁.rd ++ s₁.wr) ((FSt s₀).setWidth 64 + BitVec.ofNat 64 d) 4 :=
    fun d hd => by rw [rdwr₁]; exact in_rw (r := fstR s₀) (by simp) (Offset.contains_base _ hd (by omega_arith))
  obtain mnS : ∀ r ∈ [mnR s₀], Region.Sub r (fstR s₀) ∨ Region.Sub r (fscrR s₀) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Or.inr (Offset.sub_base _ (by decide))
  -- `finMid`.
  refine WP.seq ?_
  simp only [finMid, stk]
  refine wp_arg (s₀ := s₀) 1 rfl h₁.esp (hp.argIn h₁.rd h₁.wr (by decide)) (hp.arg_eq h₁.frame mnS (by decide))
    fun s₂ u₂ => ?_
  refine wp_xorma (a := (FSt s₀).setWidth 64) (by rw [u₂.gpr, addr_zero])
    (by rw [u₂.rd, u₂.wr]; simpa [add0] using stIn 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_xorma (a := (FSt s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [u₃.other .ecx (by decide), u₂.gpr]; exact addr_eq (by omega_arith))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact stIn 4 (by decide)) fun s₄ u₄ => ?_
  refine wp_bswap fun s₅ u₅ => wp_bswap fun s₆ u₆ => WP.block_nil ?_
  obtain g₆ : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s₆.gpr r = s₁.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2, u₅.other _ hr.1, u₄.other _ hr.2.2, u₃.other _ hr.1, u₂.other _ hr.2.1]
  obtain mem₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain ax₆ : s₆.gpr .eax ++ s₆.gpr .edx =
      byteRev64 ((s₁.gpr .edx ++ s₁.gpr .eax) ^^^ s₁.mem.readW ((FSt s₀).setWidth 64) 64) := by
    rw [u₆.gpr, u₆.other .eax (by decide), u₅.gpr, u₅.other .edx (by decide), u₄.gpr, u₄.other .eax (by decide),
      u₃.gpr, u₃.other .edx (by decide), u₂.other .eax (by decide), u₂.other .edx (by decide), u₃.mem,
      u₂.mem, bswap_xor_append,
      readW64_split s₁.mem]
  obtain esi₆ : s₆.gpr .esi = FW s₀ := by rw [g₆ _ (by decide), h₁.esi]
  obtain ebp₆ : s₆.gpr .ebp = FS s₀ := by rw [g₆ _ (by decide), h₁.ebp]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, h₁.rd]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, h₁.wr]
  obtain bp : BlockPre s₆ :=
    { sched := ⟨400, by rw [esi₆, rd₆, wr₆, hp.rd]; simp, by decide, by rw [esi₆]; exact kf⟩
      scr := ⟨640, by rw [ebp₆, wr₆, hp.wr]; simp, by decide, by rw [ebp₆]; exact sf⟩
      disj := by
        rw [esi₆, ebp₆]
        exact (hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₇ ⟨same₇, esi₇, ax₇⟩ => ?_)
  let A := (FS s₀).setWidth 64
  obtain xR₆ : xR s₆ = ⟨A, 84⟩ := by rw [xR, ebp₆]
  obtain f₇ : Frame [⟨A, 84⟩] s₁.mem s₇.mem := by rw [← mem₆, ← xR₆]; exact same₇.frame
  obtain F₇ : Frame [mnR s₀, ⟨A, 84⟩] (savedMem s₀ (FS s₀)) s₇.mem :=
    (h₁.frame.mono (by simp)).trans (f₇.mono (by simp))
  obtain F₇S : ∀ r ∈ [mnR s₀, ⟨A, 84⟩], Region.Sub r (fstR s₀) ∨ Region.Sub r (fscrR s₀) := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Or.inr (Offset.sub_base _ (by decide))
    · exact Or.inr (Region.sub_prefix (by decide))
  obtain esp₇ : s₇.gpr .esp = s₀.gpr .esp := by rw [same₇.esp, g₆ _ (by decide), h₁.esp]
  obtain ebp₇ : s₇.gpr .ebp = FS s₀ := by rw [same₇.ebp, ebp₆]
  obtain rd₇ : s₇.rd = s₀.rd := by rw [same₇.rd, rd₆]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [same₇.wr, wr₆]
  rw [WP.block_append_iff]
  refine wp_arg (s₀ := s₀) 1 rfl esp₇ (hp.argIn rd₇ wr₇ (by decide)) (hp.arg_eq F₇ F₇S (by decide))
    fun s₈ u₈ => wp_bswap fun s₉ u₉ => wp_bswap fun s₁₀ u₁₀ => ?_
  obtain stW : ∀ d, d + 4 ≤ 8 → InRegions s₁₀.wr ((FSt s₀).setWidth 64 + BitVec.ofNat 64 d) 4 := fun d hd => by
    rw [u₁₀.wr, u₉.wr, u₈.wr, wr₇, hp.wr]
    exact in_rw (r := fstR s₀) (by simp) (Offset.contains_base _ hd (by omega_arith))
  refine wp_store (a := (FSt s₀).setWidth 64) (by rw [ea_at', u₁₀.other _ (by decide), u₉.other _ (by decide),
    u₈.gpr, addr_zero]) (by simpa [add0] using stW 0 (by decide)) fun s₁₁ w₁₁ => ?_
  refine wp_store (a := (FSt s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [ea_at', w₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]; exact addr_eq (by omega_arith))
    (by rw [w₁₁.wr]; exact stW 4 (by decide)) fun s₁₂ w₁₂ => WP.block_nil ?_
  obtain ebp₁₂ : s₁₂.gpr .ebp = FS s₀ := by
    rw [w₁₂.gpr, w₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), ebp₇]
  obtain mem₁₂ : s₁₂.mem = (s₇.mem.writeW ((FSt s₀).setWidth 64) (bswap (s₇.gpr .eax))).writeW
      ((FSt s₀).setWidth 64 + BitVec.ofNat 64 4) (bswap (s₇.gpr .edx)) := by
    rw [w₁₂.mem, w₁₁.mem, w₁₁.gpr, u₁₀.gpr, u₁₀.other .eax (by decide), u₉.gpr, u₁₀.mem, u₉.mem,
      u₉.other .edx (by decide), u₈.other .eax (by decide), u₈.other .edx (by decide), u₈.mem]
  obtain rdwr₁₂ : s₁₂.rd ++ s₁₂.wr = [keyR s₀, lastR s₀, argsR s₀, fstR s₀, fscrR s₀] := by
    rw [w₁₂.rd, w₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, w₁₂.wr, w₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, rd₇, wr₇, hp.rd, hp.wr]; rfl
  obtain c0 : (fstR s₀).Contains ((FSt s₀).setWidth 64) (32 / 8) := by
    simpa [add0] using Offset.contains_base ((FSt s₀).setWidth 64) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  obtain c4 : (fstR s₀).Contains ((FSt s₀).setWidth 64 + BitVec.ofNat 64 4) (32 / 8) :=
    Offset.contains_base _ (by decide) (by omega_arith)
  obtain F₁₂ : Frame [mnR s₀, ⟨A, 84⟩, fstR s₀] (savedMem s₀ (FS s₀)) s₁₂.mem := by
    rw [mem₁₂]
    exact ((F₇.mono (by simp)).writeW (r := fstR s₀) (by simp) _ c0).writeW (r := fstR s₀) (by simp) _ c4
  -- The slots of the saved registers.
  obtain slots : ∀ d, 84 ≤ d → d + 4 ≤ 100 →
      s₁₂.mem.readW (A + BitVec.ofNat 64 d) 32 = (savedMem s₀ (FS s₀)).readW (A + BitVec.ofNat 64 d) 32 := by
    intro d h₁' h₂'
    refine F₁₂.readW (r := ⟨A + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact (hp.st_scr.sub_right (Offset.sub_base _ (by omega_arith))).symm
  obtain ret : s₁₂.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
    rw [F₁₂.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact (savedMem_frame s₀ (FS s₀)).readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_scr.sub_right (Offset.sub_base _ (by decide))
      · exact hp.ret_scr.sub_right (Region.sub_prefix (by decide))
      · exact hp.ret_st
  refine WP.mono (restore_ok ebp₁₂ (by omega_arith) (fun d h₁' h₂' => by
      rw [rdwr₁₂]; exact in_rw (r := fscrR s₀) (by simp) (Offset.contains_base _ (by omega_arith) (by omega_arith)))
      (saved_of slots))
    fun s' r' => ⟨restored r' (by
      rw [w₁₂.gpr, w₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), esp₇]) (by rw [r'.mem, ret]), ?_⟩
  intro hk msg hml hne hst
  obtain F₈ : Frame [fscrR s₀] s₀.mem s₇.mem := by
    refine ((savedMem_frame s₀ (FS s₀)).sub fun r hr => ⟨fscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩).trans
      (F₇.sub fun r hr => ⟨fscrR s₀, by simp, ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.sub_base _ (by decide)
    · exact Region.sub_prefix (by decide)
  obtain F₁ : Frame [fscrR s₀] s₀.mem s₁.mem :=
    ((savedMem_frame s₀ (FS s₀)).sub fun r hr => ⟨fscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩).trans
    (h₁.frame.sub fun r hr => ⟨fscrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by decide)⟩)
  obtain hS' : sch s₆ = Spec.TripleDes.scheduleAt s₀.mem ((FW s₀).setWidth 64) := by
    show Spec.TripleDes.scheduleAt s₆.mem ((s₆.gpr .esi).setWidth 64) = _
    rw [esi₆, mem₆]
    exact scheduleAt_frame F₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.key_scr.sub_left (Region.sub_prefix (by decide))
  obtain hst₁ : le8 (s₁.mem.readW ((FSt s₀).setWidth 64) 64) = Spec.Aes.bytesAt s₀.mem ((FSt s₀).setWidth 64) 8 := by
    rw [le8_readW]
    exact bytesAt_frame F₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_scr) (by decide)
  obtain hks := subkeys_tdes (Spec.TripleDes.scheduleAt s₀.mem ((FW s₀).setWidth 64))
  obtain hk' : Spec.Aes.bytesAt s₀.mem ((FW s₀).setWidth 64 + BitVec.ofNat 64 384) 8 ++
      Spec.Aes.bytesAt s₀.mem ((FW s₀).setWidth 64 + BitVec.ofNat 64 392) 8 =
      (Spec.Cmac.subkeys (ciphAt s₀.mem ((FW s₀).setWidth 64)) 8).1 ++
        (Spec.Cmac.subkeys (ciphAt s₀.mem ((FW s₀).setWidth 64)) 8).2 := by
    rw [show (FW s₀).setWidth 64 + BitVec.ofNat 64 392 =
        (FW s₀).setWidth 64 + BitVec.ofNat 64 384 + BitVec.ofNat 64 8 from
      (Offset.add_add _ 384 8).symm, ← bytesAt_split]; exact hk
  obtain ⟨k1, k2⟩ := List.append_inj hk' (by rw [Proof.Cmac.bytesAt_length, ciphAt, hks, length_le8])
  show Spec.Aes.bytesAt s'.mem ((FSt s₀).setWidth 64) 8 = _
  rw [r'.mem, mem₁₂, ← le8_readW, readW64_split, Mem.readW_writeW_self32, readW_lo_of_hi, bswap_eq, bswap_eq,
    byteRev32_append, ax₇, ax₆, hS', ← tdesWith_le8, le8_xor, h₁.blk, hst₁,
    macFull_split8 _ hml (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
      (by rw [Proof.Cmac.bytesAt_length]; exact hne), ← hst, ← k1, ← k2, Proof.Cmac.xor_comm]

end VG.Proof.CmacTripleDes.X86

end

end


/-!
# Streaming TDEA-CMAC on x86: the code of `init`, `update` and `finalize`, inline

The code of `vg_cmac_triple_des_init`, `_update` and `_finalize` reads its
arguments from the stack: each run inside the streaming functions is in a
frame that pushes them, the last first, and one more word in the return
address's place (`WP.frameInline`, `RelCT.frameInline`), from its contract
(`WP.inline`). For each: what it needs (`…Args`: the registers pushed, and
the regions), what it leaves (`…Post`, in terms of the memory before it),
and that two runs with the same arguments and stack pointer leak the same
(`…_rel`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86
open VG.Proof.CmacTripleDes.X86 (updateX86 finalizeX86 initX86 ciphAt scheduleAt_frame)

/-! ## Inlining in a frame -/

/-- Argument `i` of code run in a frame pushing `rs`, the last of which is in
the return address's place: the `i + 2`-th register from the end. -/
theorem pushed_arg {rs : List Reg} {s : State} (hrs : Reg.esp ∉ rs) (hn : 4 * rs.length ≤ (s.gpr .esp).toNat)
    {i : Nat} (hi : i + 1 < rs.length) : arg (pushed rs s) i = s.gpr rs[rs.length - 1 - (i + 1)] := by
  have := pushed_word hrs hn (i := i + 1) hi
  show (pushed rs s).mem.readW (((pushed rs s).gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 32 = _
  rw [show 4 + 4 * i = 4 * (i + 1) by omega_using []]
  exact this

theorem sub_add4 (x : BitVec 32) {a : Nat} (h : 4 ≤ a) (ha : a < 2 ^ 32) :
    x - BitVec.ofNat 32 a + BitVec.ofNat 32 4 = x - BitVec.ofNat 32 (a - 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- The first argument's address, in a frame of `rs`. -/
theorem pushed_argAddr0 {rs : List Reg} {s : State} {k : Nat} (hk : 4 * rs.length = k + 4) (hk' : k + 4 < 2 ^ 32) :
    argAddr (pushed rs s) 0 = (s.gpr .esp - BitVec.ofNat 32 k).setWidth 64 := by
  show ((pushed rs s).gpr .esp + BitVec.ofNat 32 4).setWidth 64 = _
  rw [pushed_esp, hk, sub_add4 _ (by omega_using []) hk', Nat.add_sub_cancel]

/-- The `a` bytes just below `E`, in a region of the `b ≥ a` bytes below it. -/
theorem cov_below {E : BitVec 32} {a b : Nat} (hab : a ≤ b) (hb : b ≤ E.toNat) :
    Covers [⟨(E - BitVec.ofNat 32 a).setWidth 64, a⟩] [below E b] :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    refine ⟨below E b, List.mem_singleton_self _, b - a, ?_, by simp; omega_using [hab]⟩
    show (E - BitVec.ofNat 32 a).setWidth 64 = (E - BitVec.ofNat 32 b).setWidth 64 + BitVec.ofNat 64 (b - a)
    apply BitVec.eq_of_toNat_eq
    have := E.isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [hab, hb]

/-- Verified code without calls, in the frame that pushes its arguments `rs`
(and a word in the return address's place), from its contract `k`: it runs
from the state after the push, with the permissions it is given; it leaves
the permissions and callee-saved registers of `s`, and changes memory only
within the regions it may write and the frame. -/
theorem WP.frameInline {rs : List Reg} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hn : c.noCalls = true) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs) {s : State}
    (hd : 4 * rs.length ≤ (s.gpr .esp).toNat) {rd wr : List Region}
    (hpre : k.pre ((pushed rs s).withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ below (s.gpr .esp) (4 * rs.length) :: s.wr))
    (hw : Covers wr (below (s.gpr .esp) (4 * rs.length) :: s.wr)) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .esp) (4 * rs.length)]) s.mem s'.mem →
      (∃ s₂ : State, Frame [below (s.gpr .esp) (4 * rs.length)] s₂.mem s'.mem ∧
        k.post ((pushed rs s).withRegions rd wr) s₂) → Q s') :
    WP isa (.frame (.push rs) c (.pop .eax rs.length)) s Q := by
  refine WP.frame hne hrs (by decide) hd hsp ?_
  refine WP.inline (k := k) hv hpre (by rw [pushed_rd, pushed_wr]; exact hc) (by rw [pushed_wr]; exact hw)
    (fun s₂ rd₂ wr₂ ha f₂ _ post₂ m u fl => ?_) hn
  refine hQ _ (by rw [popped_rd, rd₂, pushed_rd]) (by rw [popped_wr, wr₂, pushed_wr]; rfl) (fun r hr => ?_) ?_
    ⟨s₂.withRegions rd wr, by rw [State.withRegions_mem]; exact fl, post₂⟩
  · by_cases h : r = .esp
    · subst h
      rw [popped_esp, ha.1 .esp hr, pushed_esp]; exact BitVec.sub_add_cancel _ _
    · have hne' : r ≠ .eax := by
        rintro rfl; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ h hne', ha.1 r hr, pushed_gpr _ _ h]
  · exact (((pushed_frame hrs hd).mono fun r hr => List.mem_append_right _ hr).trans
      (f₂.mono fun r hr => List.mem_append_left _ hr)).trans (fl.mono fun r hr => List.mem_append_right _ hr)

/-- Two runs of such code leak the same if its contract holds in both, its
public data agree, and so does `esp`. -/
theorem RelCT.frameInline {rs : List Reg} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .esp = s₂.gpr .esp ∧
      k.pre ((pushed rs s₁).withRegions rd wr) ∧ k.pre ((pushed rs s₂).withRegions rd wr) ∧
      k.pub ((pushed rs s₁).withRegions rd wr) ((pushed rs s₂).withRegions rd wr) ∧
      Covers (rd ++ wr) (s₁.rd ++ below (s₁.gpr .esp) (4 * rs.length) :: s₁.wr) ∧
      Covers wr (below (s₁.gpr .esp) (4 * rs.length) :: s₁.wr) ∧
      Covers (rd ++ wr) (s₂.rd ++ below (s₂.gpr .esp) (4 * rs.length) :: s₂.wr) ∧
      Covers wr (below (s₂.gpr .esp) (4 * rs.length) :: s₂.wr)) :
    RelCT isa P (.frame (.push rs) c (.pop .eax rs.length)) fun _ _ => True := by
  refine VG.X86.RelCT.frame (R := fun _ _ => True) (fun s₁ s₂ h => (hP _ _ h).1) ?_
  refine relCT_inline regionModel (Post := fun s s' => abiPreserved s s' ∧ k.post s s') hv hct ?_
  rintro _ _ ⟨s₁, s₂, h, rfl, rfl⟩
  obtain ⟨-, p₁, p₂, q, c₁, w₁, c₂, w₂⟩ := hP _ _ h
  exact ⟨rd, wr, rd, wr, p₁, p₂, q,
    by show Covers _ ((pushed rs s₁).rd ++ (pushed rs s₁).wr); rw [pushed_rd, pushed_wr]; exact c₁,
    by show Covers _ (pushed rs s₁).wr; rw [pushed_wr]; exact w₁,
    by show Covers _ ((pushed rs s₂).rd ++ (pushed rs s₂).wr); rw [pushed_rd, pushed_wr]; exact c₂,
    by show Covers _ (pushed rs s₂).wr; rw [pushed_wr]; exact w₂⟩

theorem eq_ofNat {x : BitVec 32} {n : Nat} (h : x = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) : x.toNat = n := by
  rw [h, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn

/-- The bytes of a region the frame does not overlap, from the state the
frame is pushed in. -/
theorem keep_push {rs : List Reg} {s : State} (hrs : Reg.esp ∉ rs) (hd : 4 * rs.length ≤ (s.gpr .esp).toNat)
    {p : Addr} {n : Nat} (hb : (below (s.gpr .esp) (4 * rs.length)).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt (pushed rs s).mem p n = Spec.Aes.bytesAt s.mem p n :=
  Proof.Cmac.bytesAt_frame (pushed_frame hrs hd) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hb.symm) hn

/-- The return address's place and the arguments, in a frame of `b` bytes. -/
theorem ret_sub {E : BitVec 32} {b : Nat} (hb : 4 ≤ b) :
    Region.Sub ⟨(E - BitVec.ofNat 32 b).setWidth 64, 4⟩ (below E b) := Region.sub_prefix hb

theorem args_sub {E : BitVec 32} {b : Nat} (hb : 4 ≤ b) (he : b ≤ E.toNat) :
    Region.Sub ⟨(E - BitVec.ofNat 32 (b - 4)).setWidth 64, b - 4⟩ (below E b) := below_sub (by omega) he

theorem nosp_update : NoSp Impl.CmacTripleDes.X86.update := NoSp.of_all (by lit_decide)
theorem nosp_finalize : NoSp Impl.CmacTripleDes.X86.finalize := NoSp.of_all (by lit_decide)
theorem nosp_init : NoSp Impl.CmacTripleDes.X86.init := NoSp.of_all (by lit_decide)

/-! ## `update` -/

/-- The registers `updFrame` pushes. -/
abbrev rsU : List Reg := [.edi, .esi, .ebx, .edx, .eax, .ecx]

theorem hrsU : Reg.esp ∉ rsU := by decide

/-- What a run of `update` needs: the key schedule `W`, the chaining value
`C`, `n` blocks at `D` and the working space `S`, in `eax`, `edx`, `ebx`,
`esi` and `edi`. -/
structure UArgs (s : State) (W C D S : BitVec 32) (n : Nat) : Prop where
  eax : s.gpr .eax = W
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = D
  esi : s.gpr .esi = BitVec.ofNat 32 n
  edi : s.gpr .edi = S
  esp : 24 ≤ (s.gpr .esp).toNat
  hn : 8 * n < 2 ^ 32
  wc : (⟨W.setWidth 64, 384⟩ : Region).Disjoint ⟨C.setWidth 64, 8⟩
  ws : (⟨W.setWidth 64, 384⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  dc : (⟨D.setWidth 64, 8 * n⟩ : Region).Disjoint ⟨C.setWidth 64, 8⟩
  ds : (⟨D.setWidth 64, 8 * n⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  cs : (⟨C.setWidth 64, 8⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  bW : (below (s.gpr .esp) 24).Disjoint ⟨W.setWidth 64, 384⟩
  bD : (below (s.gpr .esp) 24).Disjoint ⟨D.setWidth 64, 8 * n⟩
  bC : (below (s.gpr .esp) 24).Disjoint ⟨C.setWidth 64, 8⟩
  bS : (below (s.gpr .esp) 24).Disjoint ⟨S.setWidth 64, 640⟩
  fW : W.toNat + 384 ≤ 2 ^ 32
  fC : C.toNat + 8 ≤ 2 ^ 32
  fD : D.toNat + 8 * n ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  reads : Covers [⟨W.setWidth 64, 384⟩, ⟨D.setWidth 64, 8 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨C.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩] s.wr

/-- What a run of `update` leaves. -/
structure UPost (s : State) (W C D S : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩, below (s.gpr .esp) 24] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (C.setWidth 64) 8 =
    Spec.Cmac.chain (ciphAt s.mem (W.setWidth 64)) (Spec.Aes.bytesAt s.mem (C.setWidth 64) 8)
      (Spec.Cmac.blocksAt s.mem (D.setWidth 64) 8 n)

/-- The regions the code of `update` runs with. -/
abbrev uRd (E W D : BitVec 32) (n : Nat) : List Region :=
  [⟨W.setWidth 64, 384⟩, ⟨D.setWidth 64, 8 * n⟩, ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
abbrev uWr (C S : BitVec 32) : List Region := [⟨C.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩]

/-- Covering a frame's regions, from those of the state it is pushed in. -/
theorem cov_frame {s : State} {rd₀ wr₀ : List Region} {a b : Nat} (hab : a ≤ b) (hb : b ≤ (s.gpr .esp).toNat)
    (hr : Covers rd₀ (s.rd ++ s.wr)) (hw : Covers wr₀ s.wr) :
    Covers ((rd₀ ++ [⟨(s.gpr .esp - BitVec.ofNat 32 a).setWidth 64, a⟩]) ++ wr₀)
      (s.rd ++ below (s.gpr .esp) b :: s.wr) := by
  intro x n ⟨r, hr', hcn⟩
  rcases List.mem_append.mp hr' with hr' | hr'
  · rcases List.mem_append.mp hr' with hr' | hr'
    · obtain ⟨r', hr'', hc'⟩ := hr x n ⟨r, hr', hcn⟩
      rcases List.mem_append.mp hr'' with h' | h'
      · exact ⟨r', List.mem_append_left _ h', hc'⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h'), hc'⟩
    · rw [List.mem_singleton] at hr'; subst hr'
      obtain ⟨r', hr'', hc'⟩ := cov_below hab hb x n ⟨_, List.mem_singleton_self _, hcn⟩
      rw [List.mem_singleton] at hr''; subst hr''
      exact ⟨_, List.mem_append_right _ List.mem_cons_self, hc'⟩
  · obtain ⟨r', hr'', hc'⟩ := hw x n ⟨r, hr', hcn⟩
    exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr''), hc'⟩

theorem covW_frame {s : State} {wr₀ : List Region} {b : Nat} (hw : Covers wr₀ s.wr) :
    Covers wr₀ (below (s.gpr .esp) b :: s.wr) := by
  intro x n hi
  obtain ⟨r', hr', hc'⟩ := hw x n hi
  exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

namespace UArgs
variable {s : State} {W C D S : BitVec 32} {n : Nat} (h : UArgs s W C D S n)
include h

theorem fit : 4 * rsU.length ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega_using [this]

theorem args : arg (pushed rsU s) 0 = W ∧ arg (pushed rsU s) 1 = C ∧ arg (pushed rsU s) 2 = D ∧
    arg (pushed rsU s) 3 = BitVec.ofNat 32 n ∧ arg (pushed rsU s) 4 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [pushed_arg hrsU h.fit (by decide)] <;> simp [h.eax, h.edx, h.ebx, h.esi, h.edi]

theorem pre : updateX86.pre ((pushed rsU s).withRegions (uRd (s.gpr .esp) W D n) (uWr C S)) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h.args
  obtain hN : (BitVec.ofNat 32 n).toNat = n := eq_ofNat rfl (by have := h.hn; omega_using [this])
  have he := h.esp
  obtain eA : argAddr (pushed rsU s) 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := pushed_argAddr0 (k := 20) rfl (by decide)
  obtain eSp : (pushed rsU s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 := pushed_esp _ _
  obtain bA := args_sub (E := s.gpr .esp) (b := 24) (by decide) he
  obtain bR := ret_sub (E := s.gpr .esp) (b := 24) (by decide)
  simp only [updateX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, hN]
  refine ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.bC.sub_left bA, h.bS.sub_left bA,
    h.bC.sub_left bR, h.bS.sub_left bR, h.fW, h.fC, h.fD, h.fS, ?_⟩
  rw [sub_toNat (by omega_using [he])]; have := (s.gpr .esp).isLt; omega_using []

end UArgs

theorem upd_wp {s : State} {W C D S : BitVec 32} {n : Nat} (h : UArgs s W C D S n) :
    WP isa Impl.CmacTripleDes.Stream.X86.updFrame s (UPost s W C D S n) := by
  obtain hN : (BitVec.ofNat 32 n).toNat = n := eq_ofNat rfl (by have := h.hn; omega_using [this])
  refine WP.frameInline (rs := rsU) (k := updateX86) (fun _ hs => Proof.CmacTripleDes.X86.update_wp hs)
    (by lit_decide) nosp_update (by simp) hrsU h.fit h.pre (cov_frame (by decide) h.fit h.reads h.writes)
    (covW_frame h.writes) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, -⟩ := h.args
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  simp only [updateX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, hN] at post
  rw [Proof.Cmac.bytesAt_frame m₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bC.symm) (by decide),
    post, ciphAt, ciphAt, scheduleAt_frame (pushed_frame hrsU h.fit) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bW.symm,
    keep_push hrsU h.fit h.bC (by decide)]
  congr 1
  simp only [Spec.Cmac.blocksAt]
  refine List.map_congr_left fun i hi => keep_push hrsU h.fit (h.bD.sub_right (Offset.sub_base _ ?_)) (by decide)
  rw [List.mem_range] at hi; omega_using [hi]

theorem upd_rel {W C D S E : BitVec 32} {n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S n ∧ UArgs s₂ W C D S n ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P Impl.CmacTripleDes.Stream.X86.updFrame fun _ _ => True := by
  refine RelCT.frameInline (rs := rsU) (fun _ hs => Proof.CmacTripleDes.X86.update_wp hs)
    Proof.CmacTripleDes.X86.update_ct (uRd E W D n) (uWr C S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [e₁] at p₁
  rw [e₂] at p₂
  obtain c₁ := cov_frame (s := s₁) (a := 20) (b := 24) (by decide) h₁.fit h₁.reads h₁.writes
  obtain c₂ := cov_frame (s := s₂) (a := 20) (b := 24) (by decide) h₂.fit h₂.reads h₂.writes
  obtain ⟨a0, a1, a2, a3, a4⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4⟩ := h₂.args
  refine ⟨e₁.trans e₂.symm, p₁, p₂, ⟨by simp only [State.withRegions_gpr, pushed_esp, e₁, e₂], fun i hi => ?_⟩,
    by subst e₁; exact c₁, covW_frame h₁.writes, by subst e₂; exact c₂, covW_frame h₂.writes⟩
  simp only [arg_withRegions]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

/-! ## `finalize` -/

/-- What a run of `finalize` needs: the key schedule and subkeys `K`, the
state `St`, the `L` last bytes at `P` and the working space `S`, in `eax`,
`edx`, `ebx`, `esi` and `edi`. -/
structure FArgs (s : State) (K St P S : BitVec 32) (L : Nat) : Prop where
  eax : s.gpr .eax = K
  edx : s.gpr .edx = St
  ebx : s.gpr .ebx = P
  esi : s.gpr .esi = BitVec.ofNat 32 L
  edi : s.gpr .edi = S
  len : L ≤ 8
  esp : 24 ≤ (s.gpr .esp).toNat
  kst : (⟨K.setWidth 64, 400⟩ : Region).Disjoint ⟨St.setWidth 64, 8⟩
  ks : (⟨K.setWidth 64, 400⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  pst : (⟨P.setWidth 64, L⟩ : Region).Disjoint ⟨St.setWidth 64, 8⟩
  ps : (⟨P.setWidth 64, L⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  sts : (⟨St.setWidth 64, 8⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  bK : (below (s.gpr .esp) 24).Disjoint ⟨K.setWidth 64, 400⟩
  bP : (below (s.gpr .esp) 24).Disjoint ⟨P.setWidth 64, L⟩
  bSt : (below (s.gpr .esp) 24).Disjoint ⟨St.setWidth 64, 8⟩
  bS : (below (s.gpr .esp) 24).Disjoint ⟨S.setWidth 64, 640⟩
  fK : K.toNat + 400 ≤ 2 ^ 32
  fSt : St.toNat + 8 ≤ 2 ^ 32
  fP : P.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  reads : Covers [⟨K.setWidth 64, 400⟩, ⟨P.setWidth 64, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨St.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩] s.wr

/-- What a run of `finalize` leaves. -/
structure FPost (s : State) (K St P S : BitVec 32) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩, below (s.gpr .esp) 24] s.mem s'.mem
  out : let ciph := ciphAt s.mem (K.setWidth 64)
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (K.setWidth 64 + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem (St.setWidth 64) 8 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem (St.setWidth 64) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem (P.setWidth 64) L)

/-- The regions the code of `finalize` runs with. -/
abbrev fRd (E K P : BitVec 32) (L : Nat) : List Region :=
  [⟨K.setWidth 64, 400⟩, ⟨P.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
abbrev fWr (St S : BitVec 32) : List Region := [⟨St.setWidth 64, 8⟩, ⟨S.setWidth 64, 640⟩]

namespace FArgs
variable {s : State} {K St P S : BitVec 32} {L : Nat} (h : FArgs s K St P S L)
include h

theorem fit : 4 * rsU.length ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega_using [this]

theorem args : arg (pushed rsU s) 0 = K ∧ arg (pushed rsU s) 1 = St ∧ arg (pushed rsU s) 2 = P ∧
    arg (pushed rsU s) 3 = BitVec.ofNat 32 L ∧ arg (pushed rsU s) 4 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [pushed_arg hrsU h.fit (by decide)] <;> simp [h.eax, h.edx, h.ebx, h.esi, h.edi]

theorem pre : finalizeX86.pre ((pushed rsU s).withRegions (fRd (s.gpr .esp) K P L) (fWr St S)) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h.args
  obtain hL : (BitVec.ofNat 32 L).toNat = L := eq_ofNat rfl (by have := h.len; omega_using [this])
  have he := h.esp
  obtain eA : argAddr (pushed rsU s) 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := pushed_argAddr0 (k := 20) rfl (by decide)
  obtain eSp : (pushed rsU s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 := pushed_esp _ _
  obtain bA := args_sub (E := s.gpr .esp) (b := 24) (by decide) he
  obtain bR := ret_sub (E := s.gpr .esp) (b := 24) (by decide)
  simp only [finalizeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, hL]
  refine ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.bSt.sub_left bA, h.bS.sub_left bA,
    h.bSt.sub_left bR, h.bS.sub_left bR, h.fK, h.fSt, h.fP, h.fS, ?_, h.len⟩
  rw [sub_toNat (by omega_using [he])]; have := (s.gpr .esp).isLt; omega_using []

end FArgs

theorem fin_wp {s : State} {K St P S : BitVec 32} {L : Nat} (h : FArgs s K St P S L) :
    WP isa Impl.CmacTripleDes.Stream.X86.finFrame s (FPost s K St P S L) := by
  obtain hL : (BitVec.ofNat 32 L).toNat = L := eq_ofNat rfl (by have := h.len; omega_using [this])
  refine WP.frameInline (rs := rsU) (k := finalizeX86) (fun _ hs => Proof.CmacTripleDes.X86.finalize_wp hs)
    (by lit_decide) nosp_finalize (by simp) hrsU h.fit h.pre (cov_frame (by decide) h.fit h.reads h.writes)
    (covW_frame h.writes) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, -⟩ := h.args
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  simp only [finalizeX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, hL] at post
  intro _ _ hk msg hm hne hst
  rw [Proof.Cmac.bytesAt_frame m₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.bSt.symm) (by decide)]
  obtain hsch : ciphAt (pushed rsU s).mem (K.setWidth 64) = ciphAt s.mem (K.setWidth 64) := by
    simp only [ciphAt]
    rw [scheduleAt_frame (pushed_frame hrsU h.fit) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.bK.sub_right (Region.sub_prefix (by decide))).symm]
  obtain eK2 := keep_push hrsU h.fit (p := K.setWidth 64 + 384) (n := 16)
    (h.bK.sub_right (Offset.sub_base (K.setWidth 64) (d := 384) (n := 16) (by decide))) (by decide)
  obtain eSt := keep_push hrsU h.fit h.bSt (by decide)
  obtain eP := keep_push hrsU h.fit h.bP (by have := h.len; omega_using [hL])
  rw [hsch, eK2, eSt, eP] at post
  exact post hk msg hm hne hst

theorem fin_rel {K St P S E : BitVec 32} {L : Nat} {Q : State → State → Prop}
    (h : ∀ s₁ s₂, Q s₁ s₂ → FArgs s₁ K St P S L ∧ FArgs s₂ K St P S L ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa Q Impl.CmacTripleDes.Stream.X86.finFrame fun _ _ => True := by
  refine RelCT.frameInline (rs := rsU) (fun _ hs => Proof.CmacTripleDes.X86.finalize_wp hs)
    Proof.CmacTripleDes.X86.finalize_ct (fRd E K P L) (fWr St S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [e₁] at p₁
  rw [e₂] at p₂
  obtain c₁ := cov_frame (s := s₁) (a := 20) (b := 24) (by decide) h₁.fit h₁.reads h₁.writes
  obtain c₂ := cov_frame (s := s₂) (a := 20) (b := 24) (by decide) h₂.fit h₂.reads h₂.writes
  obtain ⟨a0, a1, a2, a3, a4⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4⟩ := h₂.args
  refine ⟨e₁.trans e₂.symm, p₁, p₂, ⟨by simp only [State.withRegions_gpr, pushed_esp, e₁, e₂], fun i hi => ?_⟩,
    by subst e₁; exact c₁, covW_frame h₁.writes, by subst e₂; exact c₂, covW_frame h₂.writes⟩
  simp only [arg_withRegions]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

/-! ## `init` -/

/-- The registers `initFrame` pushes. -/
abbrev rsI : List Reg := [.edx, .eax, .ecx, .ebx, .esi]

theorem hrsI : Reg.esp ∉ rsI := by decide

/-- What a run of `init` needs: the key `Kp` of `KL` bytes, the output `O` and
the working space `S`, in `ebx`, `ecx`, `eax` and `edx`. -/
structure IArgs (s : State) (Kp O S : BitVec 32) (KL : Nat) : Prop where
  ebx : s.gpr .ebx = Kp
  ecx : s.gpr .ecx = BitVec.ofNat 32 KL
  eax : s.gpr .eax = O
  edx : s.gpr .edx = S
  klen : Spec.TripleDes.validKey KL
  esp : 20 ≤ (s.gpr .esp).toNat
  ko : (⟨Kp.setWidth 64, KL⟩ : Region).Disjoint ⟨O.setWidth 64, 400⟩
  ks : (⟨Kp.setWidth 64, KL⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  os : (⟨O.setWidth 64, 400⟩ : Region).Disjoint ⟨S.setWidth 64, 640⟩
  bK : (below (s.gpr .esp) 20).Disjoint ⟨Kp.setWidth 64, KL⟩
  bO : (below (s.gpr .esp) 20).Disjoint ⟨O.setWidth 64, 400⟩
  bS : (below (s.gpr .esp) 20).Disjoint ⟨S.setWidth 64, 640⟩
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fO : O.toNat + 400 ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  reads : Covers [⟨Kp.setWidth 64, KL⟩] (s.rd ++ s.wr)
  writes : Covers [⟨O.setWidth 64, 400⟩, ⟨S.setWidth 64, 640⟩] s.wr

/-- What a run of `init` leaves. -/
structure IPost (s : State) (Kp O S : BitVec 32) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨O.setWidth 64, 400⟩, ⟨S.setWidth 64, 640⟩, below (s.gpr .esp) 20] s.mem s'.mem
  out : let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (Kp.setWidth 64) KL)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem (O.setWidth 64) = k ∧
      Spec.Aes.bytesAt s'.mem (O.setWidth 64 + 384) 16 = ks.1 ++ ks.2

/-- The regions the code of `init` runs with. -/
abbrev iRd (E Kp : BitVec 32) (KL : Nat) : List Region :=
  [⟨Kp.setWidth 64, KL⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩]
abbrev iWr (O S : BitVec 32) : List Region := [⟨O.setWidth 64, 400⟩, ⟨S.setWidth 64, 640⟩]

theorem cov_frameI {s : State} {Kp O S : BitVec 32} {KL : Nat} (hb : 20 ≤ (s.gpr .esp).toNat)
    (hr : Covers [⟨Kp.setWidth 64, KL⟩] (s.rd ++ s.wr)) (hw : Covers (iWr O S) s.wr) :
    Covers (iRd (s.gpr .esp) Kp KL ++ iWr O S) (s.rd ++ below (s.gpr .esp) 20 :: s.wr) :=
  cov_frame (rd₀ := [⟨Kp.setWidth 64, KL⟩]) (a := 16) (b := 20) (by decide) hb hr hw

namespace IArgs
variable {s : State} {Kp O S : BitVec 32} {KL : Nat} (h : IArgs s Kp O S KL)
include h

theorem fit : 4 * rsI.length ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega_using [this]

theorem args : arg (pushed rsI s) 0 = Kp ∧ arg (pushed rsI s) 1 = BitVec.ofNat 32 KL ∧ arg (pushed rsI s) 2 = O ∧
    arg (pushed rsI s) 3 = S := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  rw [pushed_arg hrsI h.fit (by decide)] <;> simp [h.ebx, h.ecx, h.eax, h.edx]

theorem pre : initX86.pre ((pushed rsI s).withRegions (iRd (s.gpr .esp) Kp KL) (iWr O S)) := by
  obtain ⟨a0, a1, a2, a3⟩ := h.args
  obtain hK : (BitVec.ofNat 32 KL).toNat = KL := eq_ofNat rfl (by rcases h.klen with h | h <;> omega_using [h])
  have he := h.esp
  obtain eA : argAddr (pushed rsI s) 0 = (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := pushed_argAddr0 (k := 16) rfl (by decide)
  obtain eSp : (pushed rsI s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 := pushed_esp _ _
  obtain bA := args_sub (E := s.gpr .esp) (b := 20) (by decide) he
  obtain bR := ret_sub (E := s.gpr .esp) (b := 20) (by decide)
  simp only [initX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, hK]
  refine ⟨trivial, trivial, h.ko, h.ks, h.os, h.bO.sub_left bA, h.bS.sub_left bA,
    h.bO.sub_left bR, h.bS.sub_left bR, h.fK, h.fO, h.fS, ?_, h.klen⟩
  rw [sub_toNat (by omega_using [he])]; have := (s.gpr .esp).isLt; omega_using []

end IArgs

theorem init_inline_wp {s : State} {Kp O S : BitVec 32} {KL : Nat} (h : IArgs s Kp O S KL) :
    WP isa Impl.CmacTripleDes.Stream.X86.initFrame s (IPost s Kp O S KL) := by
  obtain hK : (BitVec.ofNat 32 KL).toNat = KL := eq_ofNat rfl (by rcases h.klen with h | h <;> omega_using [h])
  refine WP.frameInline (rs := rsI) (k := initX86) (fun _ hs => Proof.CmacTripleDes.X86.init_wp hs)
    (by lit_decide) nosp_init (by simp) hrsI h.fit h.pre (cov_frameI h.esp h.reads h.writes)
    (covW_frame h.writes) fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, -⟩ := h.args
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  simp only [initX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, hK] at post
  rw [← scheduleAt_frame m₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.bO.sub_right (Region.sub_prefix (by decide))).symm),
    ← Proof.Cmac.bytesAt_frame m₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.bO.sub_right
      (Offset.sub_base (O.setWidth 64) (d := 384) (n := 16) (by decide))).symm) (by decide)] at post
  obtain eK : Spec.TripleDes.bytesAt (pushed rsI s).mem (Kp.setWidth 64) KL =
      Spec.TripleDes.bytesAt s.mem (Kp.setWidth 64) KL := by
    simp only [Spec.TripleDes.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact (pushed_frame hrsI h.fit).bytes (R := ⟨Kp.setWidth 64, KL⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bK.symm)
      (by show KL ≤ 2 ^ 64; have := h.fK; omega_using [hK]) (List.mem_range.mp hi)
  rw [eK] at post
  exact post

theorem init_rel {Kp O S E : BitVec 32} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → IArgs s₁ Kp O S KL ∧ IArgs s₂ Kp O S KL ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P Impl.CmacTripleDes.Stream.X86.initFrame fun _ _ => True := by
  refine RelCT.frameInline (rs := rsI) (fun _ hs => Proof.CmacTripleDes.X86.init_wp hs)
    Proof.CmacTripleDes.X86.init_ct (iRd E Kp KL) (iWr O S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [e₁] at p₁
  rw [e₂] at p₂
  obtain c₁ := cov_frameI h₁.esp h₁.reads h₁.writes
  obtain c₂ := cov_frameI h₂.esp h₂.reads h₂.writes
  obtain ⟨a0, a1, a2, a3⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3⟩ := h₂.args
  refine ⟨e₁.trans e₂.symm, p₁, p₂, ⟨by simp only [State.withRegions_gpr, pushed_esp, e₁, e₂], fun i hi => ?_⟩,
    by subst e₁; exact c₁, covW_frame h₁.writes, by subst e₂; exact c₂, covW_frame h₂.writes⟩
  simp only [arg_withRegions]
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]

end VG.Proof.CmacTripleDes.Stream.X86
