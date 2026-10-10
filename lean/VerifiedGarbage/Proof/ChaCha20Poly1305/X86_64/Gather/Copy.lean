import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
import VerifiedGarbage.Proof.Framework.X86_64.StraightY
import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: copying a slice

Untrusted: everything here is checked by Lean. `copyBytes w` copies `rcx`
bytes from `rsi` to `rdi` (`copyBytes_ok`). Every load and store it makes
copies some bytes `[a, a + c)` of the slice to the same offsets of the
output, and every one of them starts at most where the bytes copied so far
end; copying them again leaves the first `max i (a + c)` copied (`redo`),
since the source and the output do not overlap and so the source never
changes (`src_eq`, `quad_mem`). The vector loads and stores of each width
are a `Mover` (`mover_x16` … `mover_z64`), for which two loads through
`xmm0` and `xmm1` and two stores of them are a copy of both ranges
(`quad_ok`); the general-purpose ones are `pairG_ok`.

With fewer than `2 c` bytes, `c = 2 ^ w.log`, `ladder w` copies the first
and the last `c'` bytes, `c'` the largest width at most `rcx`
(`ladderStep_ok`), or the last 3 bytes one at a time as AES-GCM's short
path does (`Proof/AesGcm/X86_64/Short/Copy.lean`, whose byte loop it
shares). Otherwise `big w` copies the first `c`, then `2 c` at a time from
an offset below `c`, while at least `2 c` remain, then the last `2 c`
(`big_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width ldW stW ld16 st16 at2 pairX pair8 pair4 copyTail copyFew
  ladderStep ladder16 ladder32 ladder quadAt big copyBytes)
open VG.Proof.AesGcm.X86_64 (succ_ofNat bytesAt_succ in_of_covers copyBody copyStep_ok src_kept length_bytesAt
  writeBytes_frame' ofNat_add_ofNat sub_beq bytesAt_frame imm_eq)
open VG.Proof.AesGcm.X86_64.Short (writeW_readW128 CopyPre)
open VG.Spec.Aes (bytesAt)

/-! ## Copying bytes again -/

theorem writeW_readW_n (m src : Mem) (a b : Addr) (n : Nat) :
    m.writeW a (src.readW b (8 * n)) = writeBytes m a (bytesAt src b n) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show 8 * n / 8 = n by omega, BitVec.setWidth_eq, BitVec.setWidth_eq, write_eq_writeBytes]
  congr 1
  simp only [bytesAt]
  exact List.map_congr_left fun j hj => Mem.extractLsb'_read _ _ (List.mem_range.mp hj)

theorem getD_bytesAt (m : Mem) (p : Addr) {n j : Nat} (h : j < n) :
    (bytesAt m p n).getD j 0 = m (p + BitVec.ofNat 64 j) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range h]

/-- Copying bytes `[a, a + c)` again, after the first `i ≥ a`: the first
`max i (a + c)`. -/
theorem redo (m : Mem) (S D : Addr) {i a c : Nat} (ha : a ≤ i) (hi : i < 2 ^ 63) (hc : a + c < 2 ^ 63) :
    writeBytes (writeBytes m D (bytesAt m S i)) (D + BitVec.ofNat 64 a) (bytesAt m (S + BitVec.ofNat 64 a) c) =
      writeBytes m D (bytesAt m S (max i (a + c))) := by
  funext x
  have hq : (x - (D + BitVec.ofNat 64 a)).toNat = ((x - D).toNat + (2 ^ 64 - a)) % 2 ^ 64 := by
    rw [show x - (D + BitVec.ofNat 64 a) = (x - D) - BitVec.ofNat 64 a from (BitVec.sub_sub _ _ _).symm,
      BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega), Nat.add_comm]
  have hlt : (x - D).toNat < 2 ^ 64 := (x - D).isLt
  simp only [writeBytes, length_bytesAt]
  generalize (x - D).toNat = d at hq hlt
  rw [hq]
  by_cases h1 : a ≤ d
  · rw [show (d + (2 ^ 64 - a)) % 2 ^ 64 = d - a by omega]
    by_cases h2 : d - a < c
    · simp only [h2, show d < max i (a + c) by omega, ↓reduceIte]
      rw [getD_bytesAt _ _ h2, getD_bytesAt _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
        Nat.add_sub_cancel' h1]
    · by_cases h3 : d < i
      · simp only [h2, h3, show d < max i (a + c) by omega, ↓reduceIte]
        rw [getD_bytesAt _ _ h3, getD_bytesAt _ _ (by omega)]
      · simp only [h2, h3, show ¬d < max i (a + c) by omega, ↓reduceIte]
  · simp only [show ¬(d + (2 ^ 64 - a)) % 2 ^ 64 < c by omega, show d < i by omega,
      show d < max i (a + c) by omega, ↓reduceIte]
    rw [getD_bytesAt _ _ (by omega), getD_bytesAt _ _ (by omega)]

theorem ea_congr {s t : State} (h : t.gpr = s.gpr) (m : MemOp) : t.ea m = s.ea m := by
  unfold State.ea; rw [h]

/-- A load of `c` bytes into a vector register and a store of one, `val`
the register's value. -/
structure Mover (c : Nat) (val : State → XReg → BitVec (8 * c)) (ld : XReg → MemOp → Instr)
    (st : MemOp → XReg → Instr) : Prop where
  ld : ∀ s x m, InRegions (s.rd ++ s.wr) (s.ea m) c → ∃ t, exec (ld x m) s = some t ∧ t.gpr = s.gpr ∧
    t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ val t x = s.mem.readW (s.ea m) (8 * c) ∧
    ∀ y, y ≠ x → val t y = val s y
  st : ∀ s m x, InRegions s.wr (s.ea m) c → ∃ t, exec (st m x) s = some t ∧ t.gpr = s.gpr ∧
    t.mem = s.mem.writeW (s.ea m) (val s x) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ val t = val s

theorem mover_x16 : Mover 16 State.xmm .movdquLoad .movdquStore where
  ld s x m h := ⟨s.setXmm x (s.mem.readW (s.ea m) 128), by simp only [exec, State.load128, h, ite_true,
    Option.map_some], rfl, rfl, rfl, rfl, xmm_setXmm_self .., fun _ hy => xmm_setXmm_of_ne _ _ hy⟩
  st s m x h := ⟨{ s with mem := s.mem.writeW (s.ea m) (s.xmm x) }, by simp only [exec, State.store128, h,
    ite_true], rfl, rfl, rfl, rfl, rfl⟩

theorem mover_v16 : Mover 16 State.xmm (.vmovdquLoad .l128) (.vmovdquStore .l128) where
  ld s x m h := ⟨s.setV .l128 x (s.mem.readW (s.ea m) 128) 0, by simp only [exec, State.load128, h, ite_true,
    Option.map_some], rfl, rfl, rfl, rfl, by simp [xmm_setV], fun _ hy => by simp [xmm_setV, hy]⟩
  st s m x h := ⟨{ s with mem := s.mem.writeW (s.ea m) (s.xmm x) }, by simp only [exec, State.store128, h,
    ite_true], rfl, rfl, rfl, rfl, rfl⟩

theorem mover_y32 : Mover 32 State.ymm (.vmovdquLoad .l256) (.vmovdquStore .l256) where
  ld s x m h := ⟨s.setV .l256 x ((s.mem.readW (s.ea m) 256).extractLsb' 0 128)
    ((s.mem.readW (s.ea m) 256).extractLsb' 128 128), by simp only [exec, State.load256, h, ite_true,
    Option.map_some],
    rfl, rfl, rfl, rfl,
    by simp only [StraightY.ymm_setV, ↓reduceIte, StraightY.split_eq], fun _ hy => by simp only [StraightY.ymm_setV, hy, ↓reduceIte]⟩
  st s m x h := ⟨{ s with mem := s.mem.writeW (s.ea m) (s.ymm x) }, by simp only [exec, State.store256, h,
    ite_true], rfl, rfl, rfl, rfl, rfl⟩

theorem mover_z64 : Mover 64 State.zmm .vmovdqu32Load .vmovdqu32Store where
  ld s x m h := ⟨s.setZ x ((s.mem.readW (s.ea m) 512).extractLsb' 0 128)
    ((s.mem.readW (s.ea m) 512).extractLsb' 128 128) ((s.mem.readW (s.ea m) 512).extractLsb' 256 128)
    ((s.mem.readW (s.ea m) 512).extractLsb' 384 128), by simp only [exec, State.load512, h, ite_true,
    Option.map_some],
    rfl, rfl, rfl, rfl,
    StraightZ.zmm_load .., fun _ hy => StraightZ.zmm_setZ_other _ hy ..⟩
  st s m x h := ⟨{ s with mem := s.mem.writeW (s.ea m) (s.zmm x) }, by simp only [exec, State.store512, h,
    ite_true], rfl, rfl, rfl, rfl, rfl⟩

/-- Two loads of `c` bytes through `xmm0` and `xmm1`, and two stores of them. -/
theorem quad_ok {c : Nat} {val : State → XReg → BitVec (8 * c)} {ld st} (mv : Mover c val ld st) (s : State)
    (m₁ m₂ m₃ m₄ : MemOp) (h₁ : InRegions (s.rd ++ s.wr) (s.ea m₁) c) (h₂ : InRegions (s.rd ++ s.wr) (s.ea m₂) c)
    (h₃ : InRegions s.wr (s.ea m₃) c) (h₄ : InRegions s.wr (s.ea m₄) c) :
    ∃ s', runBlock isa [ld .xmm0 m₁, ld .xmm1 m₂, st m₃ .xmm0, st m₄ .xmm1] s = some s' ∧
      s'.mem = writeBytes (writeBytes s.mem (s.ea m₃) (bytesAt s.mem (s.ea m₁) c)) (s.ea m₄)
        (bytesAt s.mem (s.ea m₂) c) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨t₁, e₁, g₁, m₁', rd₁, wr₁, v₁, o₁⟩ := mv.ld s .xmm0 m₁ h₁
  obtain ⟨t₂, e₂, g₂, m₂', rd₂, wr₂, v₂, o₂⟩ := mv.ld t₁ .xmm1 m₂
    (by rw [rd₁, wr₁, ea_congr g₁]; exact h₂)
  obtain ⟨t₃, e₃, g₃, m₃', rd₃, wr₃, v₃⟩ := mv.st t₂ m₃ .xmm0 (by rw [wr₂, wr₁, ea_congr g₂, ea_congr g₁]; exact h₃)
  obtain ⟨t₄, e₄, g₄, m₄', rd₄, wr₄, v₄⟩ := mv.st t₃ m₄ .xmm1
    (by rw [wr₃, wr₂, wr₁, ea_congr g₃, ea_congr g₂, ea_congr g₁]; exact h₄)
  refine ⟨t₄, by simp only [runBlock_cons, e₁, e₂, e₃, e₄, runStep_some, runBlock_nil], ?_,
    by rw [g₄, g₃, g₂, g₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  rw [m₄', m₃', v₃, o₂ _ (by decide), v₁, v₂, m₂', m₁', ea_congr g₃, ea_congr g₂, ea_congr g₁, ea_congr g₂,
    ea_congr g₁, ea_congr g₁, writeW_readW_n, writeW_readW_n]

/-- One load and one store. -/
theorem pair1_ok {c : Nat} {val : State → XReg → BitVec (8 * c)} {ld st} (mv : Mover c val ld st) (s : State)
    (m₁ m₃ : MemOp) (h₁ : InRegions (s.rd ++ s.wr) (s.ea m₁) c) (h₃ : InRegions s.wr (s.ea m₃) c) :
    ∃ s', runBlock isa [ld .xmm0 m₁, st m₃ .xmm0] s = some s' ∧
      s'.mem = writeBytes s.mem (s.ea m₃) (bytesAt s.mem (s.ea m₁) c) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨t₁, e₁, g₁, m₁', rd₁, wr₁, v₁, -⟩ := mv.ld s .xmm0 m₁ h₁
  obtain ⟨t₃, e₃, g₃, m₃', rd₃, wr₃, -⟩ := mv.st t₁ m₃ .xmm0 (by rw [wr₁, ea_congr g₁]; exact h₃)
  refine ⟨t₃, by simp only [runBlock_cons, e₁, e₃, runStep_some, runBlock_nil], ?_,
    by rw [g₃, g₁], by rw [rd₃, rd₁], by rw [wr₃, wr₁]⟩
  rw [m₃', v₁, m₁', ea_congr g₁, writeW_readW_n]


theorem mover_l128 : Mover 16 State.xmm (.vmovdquLoad .l128) (.vmovdquStore .l128) := mover_v16

/-- The vector loads and stores of `w`'s width. -/
def valW : (w : Width) → State → XReg → BitVec (8 * 2 ^ w.log)
  | .x16 => State.xmm
  | .y32 => State.ymm
  | .z64 => State.zmm

theorem mover_w : (w : Width) → Mover (2 ^ w.log) (valW w) (ldW w) (stW w)
  | .x16 => mover_x16
  | .y32 => mover_y32
  | .z64 => mover_z64

theorem ea_keep {s t : State} {m : MemOp} (hb : t.gpr m.base = s.gpr m.base)
    (hi : ∀ r, m.index = some r → t.gpr r = s.gpr r) : t.ea m = s.ea m := by
  unfold State.ea
  cases hm : m.index with
  | none => rw [hb]
  | some r => simp only [hb, hi r hm]

/-- A load of `c` bytes into a general-purpose register and a store of one,
`val` the register's value. -/
structure GMover (c : Nat) (val : State → Reg → BitVec (8 * c)) (ld : Reg → MemOp → Instr)
    (st : MemOp → Reg → Instr) : Prop where
  ld : ∀ s x m, InRegions (s.rd ++ s.wr) (s.ea m) c → ∃ t, exec (ld x m) s = some t ∧
    (∀ r, r ≠ x → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    val t x = s.mem.readW (s.ea m) (8 * c) ∧ ∀ y, y ≠ x → val t y = val s y
  st : ∀ s m x, InRegions s.wr (s.ea m) c → ∃ t, exec (st m x) s = some t ∧ t.gpr = s.gpr ∧
    t.mem = s.mem.writeW (s.ea m) (val s x) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ val t = val s

theorem gmover_8 : GMover 8 State.gpr (fun r m => .mov r (.mem m)) .store where
  ld s x m h := ⟨s.setReg x (s.mem.readW (s.ea m) 64), by simp only [exec, readSrc, State.load64, h, ite_true,
    Option.map_some], fun _ hr => gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, gpr_setReg_self .., fun _ hy =>
    gpr_setReg_of_ne _ _ hy⟩
  st s m x h := ⟨{ s with mem := s.mem.writeW (s.ea m) (s.gpr x) }, by simp only [exec, State.store64, h,
    ite_true], rfl, rfl, rfl, rfl, rfl⟩

theorem gmover_4 : GMover 4 (fun s r => (s.gpr r).setWidth 32) (fun r m => .mov32 r (.mem m)) .store32 where
  ld s x m h := ⟨s.setReg32 x (s.mem.readW (s.ea m) 32), by simp only [exec, readSrc32, State.load32, h,
    ite_true, Option.map_some], fun _ hr => gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl,
    by simp only [State.setReg32, gpr_setReg_self, setWidth_setWidth_32], fun _ hy => by
      simp only [State.setReg32, gpr_setReg_of_ne _ _ hy]⟩
  st s m x h := ⟨{ s with mem := s.mem.writeW (s.ea m) ((s.gpr x).setWidth 32) }, by
    simp only [exec, State.store32, h, ite_true], rfl, rfl, rfl, rfl, rfl⟩

/-! ## Addresses -/

theorem ea_at0 (s : State) {b : Reg} {B : Addr} (hb : s.gpr b = B) : s.ea (at_ b 0) = B + BitVec.ofNat 64 0 := by
  simp [State.ea, at_, hb]

theorem ea_at2 (s : State) {b i : Reg} {B : Addr} {k : Nat} (hb : s.gpr b = B) (hi : s.gpr i = BitVec.ofNat 64 k)
    {d : Int} {e : Nat} (he : (k : Int) + d = e) : s.ea (at2 b i d) = B + BitVec.ofNat 64 e := by
  simp only [State.ea, at2, hb, hi, BitVec.mul_one, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

/-- No register but `rax`, `r8` and `r10` changed; the memory, `rd` and `wr`
as in `s`. -/
structure Same (s t : State) : Prop where
  gpr : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- The first `i` bytes copied, and the registers but `rax`, `r8` and `r10`
kept. -/
structure Copied (s : State) (S D : Addr) (i : Nat) (t : State) : Prop where
  r10 : t.gpr .r10 = BitVec.ofNat 64 i
  mem : t.mem = writeBytes s.mem D (bytesAt s.mem S i)
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- What the copy needs, and what it leaves: the `n` bytes at `S` copied to
`D`. -/
def CopyPost (s : State) (S D : Addr) (n : Nat) (s' : State) : Prop :=
  s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
    (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

section
variable {s : State} {S D : Addr} {n : Nat} (h : CopyPre s S D n)
include h

/-- `copyTail`: from `16 ⌊n / 16⌋` bytes copied, all `n`. -/
theorem copyTail_ok {t : State} (ht : Copied s S D (16 * (n / 16)) t) :
    WP isa copyTail t (CopyPost s S D n) := by
  have hn63 := h.lt
  have hq : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hcx : t.gpr .rcx = BitVec.ofNat 64 n := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rcx]
  refine WP.seq (WP.mono (Q := fun (u : State) => u.zf = some (decide (16 * (n / 16) = n)) ∧ u.gpr = t.gpr ∧
      u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr) ?_ fun u ⟨zf₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  · apply WP.of_runBlock
    refine ⟨_, by xrun [ht.r10, hcx], ?_⟩
    refine ⟨?_, by simp [gpr_arithFlags], rfl, rfl, rfl⟩
    simp only [zf_arithFlags]; rw [sub_beq (by omega) (by omega)]
  refine WP.ite (decide (16 * (n / 16) = n)) (by simp only [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · have hq' : 16 * (n / 16) = n := of_decide_eq_true hz
    exact WP.block_nil ⟨by rw [m₃, ht.mem, hq'], fun r a b c => by rw [g₃, ht.keep r a b c], by rw [rd₃, ht.rd],
      by rw [wr₃, ht.wr]⟩
  · have hq' : 16 * (n / 16) < n := by have := of_decide_eq_false hz; omega
    refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
      (fun (k : Nat) (v : State) => ∃ i, k = n - i ∧ i < n ∧ v.gpr .r10 = BitVec.ofNat 64 i ∧
        v.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
        (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → v.gpr r = s.gpr r) ∧ v.rd = s.rd ∧ v.wr = s.wr) ?_
      (n - 16 * (n / 16)) _
      ⟨16 * (n / 16), rfl, hq', by rw [g₃, ht.r10], by rw [m₃, ht.mem], fun r a b c => by rw [g₃, ht.keep r a b c],
        by rw [rd₃, ht.rd], by rw [wr₃, ht.wr]⟩
    rintro k v ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
    obtain ⟨v', run', mem', r10', zf', g', rd', wr'⟩ := copyStep_ok v
      (by rw [g _ (by decide) (by decide) (by decide), h.rsi])
      (by rw [g _ (by decide) (by decide) (by decide), h.rdi]) r10
      (by rw [g _ (by decide) (by decide) (by decide), h.rcx])
      (by rw [rd, wr]; exact in_of_covers h.rd hi (by omega))
      (by rw [wr]; exact in_of_covers h.wr hi (by omega))
    refine WP.of_runBlock ⟨v', run', ?_⟩
    have hlen : (bytesAt s.mem S i).length = i := length_bytesAt _ _ _
    have hmem : v'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
      rw [mem', mem, src_kept h.disj hi h.lt _ hlen, bytesAt_succ,
        writeBytes_snoc s.mem D (bytesAt s.mem S i) _ (by rw [hlen]; omega), hlen]
    have hz : v'.zf = some (decide (i + 1 = n)) := by
      rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    have gg : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → v'.gpr r = s.gpr r := fun r a b c => by
      rw [g' r a c, g r a b c]
    by_cases he : i + 1 = n
    · left
      exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
    · right
      exact ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat],
        hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩


theorem rdIn {a c : Nat} (hc : a + c ≤ n) : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 a) c :=
  h.rd _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base S hc (by have := h.lt; omega)⟩

theorem wrIn {a c : Nat} (hc : a + c ≤ n) : InRegions s.wr (D + BitVec.ofNat 64 a) c :=
  h.wr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base D hc (by have := h.lt; omega)⟩

/-- The source, after the first `i` bytes are copied: as it was. -/
theorem src_eq {u : Mem} {i a c : Nat} (hu : u = writeBytes s.mem D (bytesAt s.mem S i)) (hi : i ≤ n)
    (hc : a + c ≤ n) : bytesAt u (S + BitVec.ofNat 64 a) c = bytesAt s.mem (S + BitVec.ofNat 64 a) c := by
  have := h.lt
  subst hu
  refine bytesAt_frame (writeBytes_frame' s.mem (length_bytesAt _ _ _)) (fun r hr => ?_) (by omega)
  simp only [List.mem_singleton] at hr; subst hr
  exact (h.disj.sub_left (Offset.sub_base S hc)).sub_right (Region.sub_prefix hi)

/-- Bytes `[a₁, a₁ + c)` and `[a₂, a₂ + c)` copied after the first `i`, each
starting at most where the bytes copied so far end. -/
theorem quad_mem {u : Mem} {i a₁ a₂ c : Nat} (hu : u = writeBytes s.mem D (bytesAt s.mem S i)) (hi : i ≤ n)
    (h₁ : a₁ ≤ i) (h₂ : a₂ ≤ max i (a₁ + c)) (hc₁ : a₁ + c ≤ n) (hc₂ : a₂ + c ≤ n) :
    writeBytes (writeBytes u (D + BitVec.ofNat 64 a₁) (bytesAt u (S + BitVec.ofNat 64 a₁) c))
        (D + BitVec.ofNat 64 a₂) (bytesAt u (S + BitVec.ofNat 64 a₂) c) =
      writeBytes s.mem D (bytesAt s.mem S (max (max i (a₁ + c)) (a₂ + c))) := by
  have := h.lt
  rw [src_eq h hu hi hc₁, src_eq h hu hi hc₂, hu, redo _ _ _ h₁ (by omega) (by omega),
    redo _ _ _ h₂ (by omega) (by omega)]

omit h in
theorem mem_zero : writeBytes s.mem D (bytesAt s.mem S 0) = s.mem := by
  simp [bytesAt, writeBytes_nil]

/-! ## Fewer than `2 c` bytes -/

/-- Two vector copies, of the first and the last `c` bytes. -/
theorem pairX_ok {c : Nat} {val : State → XReg → BitVec (8 * c)} {ld st} (mv : Mover c val ld st) {t : State}
    (ht : Same s t) (hc : c ≤ n) (h2 : n ≤ 2 * c) : WP isa (.block (pairX c ld st)) t (CopyPost s S D n) := by
  have := h.lt
  have e₁ := ea_at0 t (by rw [ht.gpr .rsi (by decide) (by decide) (by decide), h.rsi])
  have e₂ := ea_at2 t (d := -(c : Int)) (e := n - c) (by rw [ht.gpr .rsi (by decide) (by decide) (by decide), h.rsi])
    (by rw [ht.gpr .rcx (by decide) (by decide) (by decide), h.rcx]) (by omega)
  have e₃ := ea_at0 t (by rw [ht.gpr .rdi (by decide) (by decide) (by decide), h.rdi])
  have e₄ := ea_at2 t (d := -(c : Int)) (e := n - c) (by rw [ht.gpr .rdi (by decide) (by decide) (by decide), h.rdi])
    (by rw [ht.gpr .rcx (by decide) (by decide) (by decide), h.rcx]) (by omega)
  obtain ⟨t', run, m', g', rd', wr'⟩ := quad_ok mv t _ _ _ _
    (by rw [e₁, ht.rd, ht.wr]; exact rdIn h (by omega)) (by rw [e₂, ht.rd, ht.wr]; exact rdIn h (by omega))
    (by rw [e₃, ht.wr]; exact wrIn h (by omega)) (by rw [e₄, ht.wr]; exact wrIn h (by omega))
  refine WP.of_runBlock ⟨t', run, ?_, fun r a b c => by rw [g', ht.gpr r a b c], by rw [rd', ht.rd],
    by rw [wr', ht.wr]⟩
  rw [m', e₁, e₂, e₃, e₄, quad_mem h (i := 0) (by rw [ht.mem, mem_zero]) (by omega) (by omega) (by omega)
    (by omega) (by omega), show max (max 0 (0 + c)) (n - c + c) = n by omega]

/-- The same with `rax` and `r8`, `c` (8 or 4) bytes at a time. -/
theorem pairG_ok {c : Nat} {val : State → Reg → BitVec (8 * c)} {ld st} (mv : GMover c val ld st) {t : State}
    (ht : Same s t) (hc : c ≤ n) (h2 : n ≤ 2 * c) :
    WP isa (.block [ld .rax (at_ .rsi 0), ld .r8 (at2 .rsi .rcx (-(c : Int))), st (at_ .rdi 0) .rax,
      st (at2 .rdi .rcx (-(c : Int))) .r8]) t (CopyPost s S D n) := by
  have := h.lt
  have hS := ht.gpr .rsi (by decide) (by decide) (by decide)
  have hD := ht.gpr .rdi (by decide) (by decide) (by decide)
  have hC := ht.gpr .rcx (by decide) (by decide) (by decide)
  rw [h.rsi] at hS; rw [h.rdi] at hD; rw [h.rcx] at hC
  have e₁ := ea_at0 t hS
  have e₂ := ea_at2 t (d := -(c : Int)) (e := n - c) hS hC (by omega)
  have e₃ := ea_at0 t hD
  have e₄ := ea_at2 t (d := -(c : Int)) (e := n - c) hD hC (by omega)
  obtain ⟨t₁, x₁, g₁, m₁, rd₁, wr₁, v₁, o₁⟩ := mv.ld t .rax _ (by rw [e₁, ht.rd, ht.wr]; exact rdIn h (by omega))
  have k₁ : ∀ m : MemOp, m.base ≠ .rax → (∀ r, m.index = some r → r ≠ .rax) → t₁.ea m = t.ea m :=
    fun m hb hi => ea_keep (g₁ _ hb) fun r hr => g₁ r (hi r hr)
  have f₁ : t₁.ea (at2 .rsi .rcx (-(c : Int))) = t.ea (at2 .rsi .rcx (-(c : Int))) :=
    k₁ _ (by simp [at2]) (by simp [at2])
  obtain ⟨t₂, x₂, g₂, m₂, rd₂, wr₂, v₂, o₂⟩ := mv.ld t₁ .r8 (at2 .rsi .rcx (-(c : Int)))
    (by rw [rd₁, wr₁, f₁, e₂, ht.rd, ht.wr]; exact rdIn h (by omega))
  have k₂ : ∀ m : MemOp, m.base ≠ .rax → m.base ≠ .r8 → (∀ r, m.index = some r → r ≠ .rax ∧ r ≠ .r8) →
      t₂.ea m = t.ea m := fun m hb hb' hi => by
    rw [ea_keep (g₂ _ hb') fun r hr => g₂ r (hi r hr).2, k₁ m hb fun r hr => (hi r hr).1]
  have f₃ : t₂.ea (at_ .rdi 0) = t.ea (at_ .rdi 0) := k₂ _ (by decide) (by decide) (by decide)
  have f₄ : t₂.ea (at2 .rdi .rcx (-(c : Int))) = t.ea (at2 .rdi .rcx (-(c : Int))) :=
    k₂ _ (by simp [at2]) (by simp [at2]) (by simp [at2])
  obtain ⟨t₃, x₃, g₃, m₃, rd₃, wr₃, v₃⟩ := mv.st t₂ (at_ .rdi 0) .rax
    (by rw [wr₂, wr₁, f₃, e₃, ht.wr]; exact wrIn h (by omega))
  obtain ⟨t₄, x₄, g₄, m₄, rd₄, wr₄, v₄⟩ := mv.st t₃ (at2 .rdi .rcx (-(c : Int))) .r8
    (by rw [wr₃, wr₂, wr₁, ea_congr g₃, f₄, e₄, ht.wr]; exact wrIn h (by omega))
  refine WP.of_runBlock ⟨t₄, by simp only [runBlock_cons, x₁, x₂, x₃, x₄, runStep_some, runBlock_nil], ?_,
    fun r a b c' => ?_, by rw [rd₄, rd₃, rd₂, rd₁, ht.rd], by rw [wr₄, wr₃, wr₂, wr₁, ht.wr]⟩
  · rw [m₄, m₃, v₃, o₂ _ (by decide), v₁, v₂, m₂, m₁, ea_congr g₃, f₄, f₃, f₁, e₁, e₂, e₃, e₄,
      writeW_readW_n, writeW_readW_n,
      quad_mem h (i := 0) (by rw [ht.mem, mem_zero]) (by omega) (by omega) (by omega) (by omega) (by omega),
      show max (max 0 (0 + c)) (n - c + c) = n by omega]
  · rw [g₄, g₃, g₂ r b, g₁ r a, ht.gpr r a b c']

/-- `cmp rcx, c`: `CF` tells whether `n < c`. -/
theorem cmpRcx_ok {c : Nat} (hc : c < 2 ^ 31) {t : State} (ht : Same s t) :
    WP isa (.block [.alu .cmp .rcx (imm c)]) t fun u => u.cf = some (decide (n < c)) ∧ Same s u := by
  have := h.lt
  have hC : t.gpr .rcx = BitVec.ofNat 64 n := by rw [ht.gpr .rcx (by decide) (by decide) (by decide), h.rcx]
  apply WP.of_runBlock
  refine ⟨_, by xrun [hC], ?_, ⟨fun r a b c => ?_, ?_, ?_, ?_⟩⟩
  · rw [cf_arithFlags, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  · rw [gpr_arithFlags, ht.gpr r a b c]
  · exact ht.mem
  · exact ht.rd
  · exact ht.wr

/-- `ladderStep c pair rest`: `rest` below `c` bytes, else `pair`. -/
theorem ladderStep_ok {c : Nat} {pair : List Instr} {rest : Prog isa} (hc : c < 2 ^ 31)
    (hr : ∀ t, Same s t → n < c → WP isa rest t (CopyPost s S D n))
    (hp : ∀ t, Same s t → c ≤ n → WP isa (.block pair) t (CopyPost s S D n)) {t : State} (ht : Same s t) :
    WP isa (ladderStep c pair rest) t (CopyPost s S D n) :=
  WP.seq (WP.mono (cmpRcx_ok h hc ht) fun u ⟨cf, hu⟩ =>
    WP.ite (decide (n < c)) (by simp only [eval, cf]) (fun hb => hr u hu (of_decide_eq_true hb))
      (fun hb => hp u hu (by have := of_decide_eq_false hb; omega)))

/-- Fewer than 4 bytes, one at a time. -/
theorem copyFew_ok {t : State} (ht : Same s t) (h4 : n < 4) : WP isa copyFew t (CopyPost s S D n) := by
  have h0 : n / 16 = 0 := by omega
  refine WP.seq (WP.mono (Q := Copied s S D (16 * (n / 16))) ?_ fun u hu => copyTail_ok h hu)
  apply WP.of_runBlock
  refine ⟨_, by xrun [], ⟨?_, ?_, fun r a b c => ?_, ?_, ?_⟩⟩
  · simp [gpr_setReg, h0]
  · rw [mem_setReg, ht.mem, h0, Nat.mul_zero, mem_zero]
  · simp [gpr_setReg, c, ht.gpr r a b c]
  · exact ht.rd
  · exact ht.wr

/-- Fewer than 16 bytes. -/
theorem ladder16_ok (h16 : n < 16) {t : State} (ht : Same s t) : WP isa ladder16 t (CopyPost s S D n) :=
  ladderStep_ok h (by decide)
    (fun _ ht h8 => ladderStep_ok h (by decide) (fun _ ht h4 => copyFew_ok h ht h4)
      (fun _ ht h4 => pairG_ok h gmover_4 ht h4 (by omega)) ht)
    (fun _ ht h8 => pairG_ok h gmover_8 ht h8 (by omega)) ht

/-- Fewer than 64 bytes. -/
theorem ladder32_ok (h64 : n < 64) {t : State} (ht : Same s t) : WP isa ladder32 t (CopyPost s S D n) :=
  ladderStep_ok h (by decide)
    (fun _ ht h32 => ladderStep_ok h (by decide) (fun _ ht h16 => ladder16_ok h h16 ht)
      (fun _ ht h16 => pairX_ok h mover_l128 ht h16 (by omega)) ht)
    (fun _ ht h32 => pairX_ok h mover_y32 ht h32 (by omega)) ht

/-- Fewer than `2 c` bytes. -/
theorem ladder_ok (w : Width) (hn : n < 2 * 2 ^ w.log) {t : State} (ht : Same s t) :
    WP isa (ladder w) t (CopyPost s S D n) := by
  cases w with
  | x16 =>
    exact ladderStep_ok h (by decide) (fun _ ht h16 => ladder16_ok h h16 ht)
      (fun _ ht h16 => pairX_ok h mover_x16 ht h16 (by simp [Width.log] at hn; omega)) ht
  | y32 => exact ladder32_ok h (by simp [Width.log] at hn; omega) ht
  | z64 =>
    exact ladderStep_ok h (by decide) (fun _ ht h64 => ladder32_ok h h64 ht)
      (fun _ ht h64 => pairX_ok h mover_z64 ht h64 (by simp [Width.log] at hn; omega)) ht

/-! ## At least `2 c` bytes -/

omit h in
theorem log_le (w : Width) : 2 ^ w.log ≤ 64 := by cases w <;> decide

/-- The loop's setup: `r10` the first offset `a < c` at which the stores are
aligned, `r8 = n - 2 c`, and `CF` whether there is no `2 c` bytes from `a`. -/
theorem bigSetup_ok (w : Width) (h2 : 2 * 2 ^ w.log ≤ n) {t : State} (ht : CopyPost s S D (2 ^ w.log) t) :
    WP isa (.block [.mov32 .r10 (imm 0), .alu .sub .r10 (.reg .rdi), .alu .and .r10 (imm (2 ^ w.log - 1)),
      .mov .r8 (.reg .rcx), .alu .sub .r8 (imm (2 * 2 ^ w.log)), .alu .cmp .r8 (.reg .r10)]) t fun u =>
      ∃ a, a < 2 ^ w.log ∧ u.gpr .r10 = BitVec.ofNat 64 a ∧ u.gpr .r8 = BitVec.ofNat 64 (n - 2 * 2 ^ w.log) ∧
        u.cf = some (decide (n - 2 * 2 ^ w.log < a)) ∧ CopyPost s S D (2 ^ w.log) u := by
  have := h.lt
  have hw := log_le w
  have hD : t.gpr .rdi = D := by rw [ht.2.1 .rdi (by decide) (by decide) (by decide), h.rdi]
  have hC : t.gpr .rcx = BitVec.ofNat 64 n := by rw [ht.2.1 .rcx (by decide) (by decide) (by decide), h.rcx]
  apply WP.of_runBlock
  have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (2 * 2 ^ w.log) = BitVec.ofNat 64 (n - 2 * 2 ^ w.log) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine ⟨_, by xrun [hD, hC, hsub], ?_⟩
  generalize hx : (BitVec.setWidth 64 0#32 - D &&& BitVec.ofNat 64 (2 ^ w.log - 1)) = x
  have hxl : x.toNat < 2 ^ w.log := by
    rw [← hx, BitVec.toNat_and]
    refine Nat.lt_of_le_of_lt Nat.and_le_right ?_
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have := Nat.two_pow_pos w.log
    omega
  refine ⟨x.toNat, hxl, ?_, ?_, ?_, ?_, fun r a b c => ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [cf_arithFlags, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  · simpa [mem_setReg, mem_arithFlags] using ht.1
  · simpa [gpr_setReg, gpr_arithFlags, a, b, c] using ht.2.1 r a b c
  · simpa only [rd_setReg, rd_arithFlags] using ht.2.2.1
  · simpa only [wr_setReg, wr_arithFlags] using ht.2.2.2

omit h in
theorem pow_int (w : Width) : ((2 : Int) ^ w.log) = ((2 ^ w.log : Nat) : Int) := by
  rw [Int.natCast_pow]; rfl

/-- `quadAt w r d`: bytes `[a, a + 2 c)`, `a = r + d`, copied after the first
`i ≥ a`. -/
theorem quadAt_ok (w : Width) {t : State} {i : Nat} (ht : CopyPost s S D i t) (hi : i ≤ n) {r : Reg} {k : Nat}
    (hr : t.gpr r = BitVec.ofNat 64 k) {d : Int} {a : Nat} (hk : (k : Int) + d = a) (h₁ : a ≤ i)
    (h₂ : a + 2 * 2 ^ w.log ≤ n) :
    WP isa (.block (quadAt w r d)) t fun u => CopyPost s S D (max i (a + 2 * 2 ^ w.log)) u ∧ u.gpr = t.gpr := by
  have := h.lt
  have hS : t.gpr .rsi = S := by rw [ht.2.1 .rsi (by decide) (by decide) (by decide), h.rsi]
  have hD : t.gpr .rdi = D := by rw [ht.2.1 .rdi (by decide) (by decide) (by decide), h.rdi]
  have hk' : (k : Int) + (d + 2 ^ w.log) = ((a + 2 ^ w.log : Nat) : Int) := by rw [pow_int]; omega
  have e₁ := ea_at2 t hS hr hk
  have e₂ := ea_at2 t hS hr hk'
  have e₃ := ea_at2 t hD hr hk
  have e₄ := ea_at2 t hD hr hk'
  obtain ⟨t', run, m', g', rd', wr'⟩ := quad_ok (mover_w w) t _ _ _ _
    (by rw [e₁, ht.2.2.1, ht.2.2.2]; exact rdIn h (by omega))
    (by rw [e₂, ht.2.2.1, ht.2.2.2]; exact rdIn h (by omega))
    (by rw [e₃, ht.2.2.2]; exact wrIn h (by omega)) (by rw [e₄, ht.2.2.2]; exact wrIn h (by omega))
  refine WP.of_runBlock ⟨t', run, ⟨?_, fun r a b c => by rw [g', ht.2.1 r a b c], by rw [rd', ht.2.2.1],
    by rw [wr', ht.2.2.2]⟩, g'⟩
  rw [m', e₁, e₂, e₃, e₄, quad_mem h ht.1 hi h₁ (by omega) (by omega) (by omega),
    show max (max i (a + 2 ^ w.log)) (a + 2 ^ w.log + 2 ^ w.log) = max i (a + 2 * 2 ^ w.log) by omega]

/-- The end of the loop's body: `r10` past the bytes copied, and `CF`
whether fewer than `2 c` bytes remain after them. -/
theorem step_ok (w : Width) {j i : Nat} (hj : j + 2 * 2 ^ w.log ≤ n) {t : State} (ht : CopyPost s S D i t)
    (r10 : t.gpr .r10 = BitVec.ofNat 64 j) (r8 : t.gpr .r8 = BitVec.ofNat 64 (n - 2 * 2 ^ w.log)) :
    WP isa (.block [.alu .add .r10 (imm (2 * 2 ^ w.log)), .alu .cmp .r8 (.reg .r10)]) t fun u =>
      u.gpr .r10 = BitVec.ofNat 64 (j + 2 * 2 ^ w.log) ∧ u.gpr .r8 = BitVec.ofNat 64 (n - 2 * 2 ^ w.log) ∧
        u.cf = some (decide (n - 2 * 2 ^ w.log < j + 2 * 2 ^ w.log)) ∧ CopyPost s S D i u := by
  have := h.lt
  have hw := log_le w
  apply WP.of_runBlock
  refine ⟨_, by xrun [r10, r8, ofNat_add_ofNat], ?_, ?_, ?_, ?_, fun r r₁ r₂ r₃ => ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, r8]
  · rw [cf_arithFlags, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  · rw [mem_arithFlags, mem_setReg, mem_arithFlags]; exact ht.1
  · simp [gpr_setReg, gpr_arithFlags, r₃, ht.2.1 r r₁ r₂ r₃]
  · rw [rd_arithFlags, rd_setReg, rd_arithFlags]; exact ht.2.2.1
  · rw [wr_arithFlags, wr_setReg, wr_arithFlags]; exact ht.2.2.2

/-- `big w`: at least `2 c` bytes. -/
theorem big_ok (w : Width) (h2 : 2 * 2 ^ w.log ≤ n) {t : State} (ht : Same s t) :
    WP isa (big w) t (CopyPost s S D n) := by
  have := h.lt
  have hw := log_le w
  have hc := Nat.two_pow_pos w.log
  -- The first `c` bytes.
  refine WP.seq (WP.mono (Q := CopyPost s S D (2 ^ w.log)) ?_ fun t₁ ht₁ => ?_)
  · have e₁ := ea_at0 t (by rw [ht.gpr .rsi (by decide) (by decide) (by decide), h.rsi])
    have e₃ := ea_at0 t (by rw [ht.gpr .rdi (by decide) (by decide) (by decide), h.rdi])
    obtain ⟨t', run, m', g', rd', wr'⟩ := pair1_ok (mover_w w) t _ _
      (by rw [e₁, ht.rd, ht.wr]; exact rdIn h (by omega)) (by rw [e₃, ht.wr]; exact wrIn h (by omega))
    refine WP.of_runBlock ⟨t', run, ?_, fun r a b c => by rw [g', ht.gpr r a b c], by rw [rd', ht.rd],
      by rw [wr', ht.wr]⟩
    have := redo s.mem S D (i := 0) (a := 0) (c := 2 ^ w.log) (Nat.le_refl _) (by omega) (by omega)
    rw [mem_zero, Nat.max_eq_right (by omega), Nat.zero_add] at this
    rw [m', e₁, e₃, ht.mem, this]
  refine WP.seq (WP.mono (bigSetup_ok h w h2 ht₁) fun t₂ ⟨a, ha, r10₂, r8₂, cf₂, ht₂⟩ => ?_)
  -- The aligned loop, from `a`.
  refine WP.seq (WP.mono (Q := fun u => ∃ i, n - 2 * 2 ^ w.log ≤ i ∧ i ≤ n ∧ CopyPost s S D i u) ?_
    fun t₃ ⟨i, hi₁, hi₂, ht₃⟩ => ?_)
  · refine WP.ite (decide (n - 2 * 2 ^ w.log < a)) (by simp only [eval, cf₂]) (fun hb => ?_) (fun hb => ?_)
    · have := of_decide_eq_true hb
      exact WP.block_nil ⟨2 ^ w.log, by omega, by omega, ht₂⟩
    · have hle : a + 2 * 2 ^ w.log ≤ n := by have := of_decide_eq_false hb; omega
      refine WP.loop (M := isa) (fun (k : Nat) (u : State) => ∃ j, k = n - j ∧ j + 2 * 2 ^ w.log ≤ n ∧
          u.gpr .r10 = BitVec.ofNat 64 j ∧ u.gpr .r8 = BitVec.ofNat 64 (n - 2 * 2 ^ w.log) ∧
          CopyPost s S D (max (2 ^ w.log) j) u) ?_ (n - a) t₂
        ⟨a, rfl, hle, r10₂, r8₂, by rw [Nat.max_eq_left (by omega)]; exact ht₂⟩
      rintro k u ⟨j, rfl, hj, r10, r8, hu⟩
      refine WP.seq (WP.mono (quadAt_ok h w hu (by omega) r10 (d := 0) (a := j) (by omega) (by omega) hj)
        fun u' ⟨hu', g'⟩ => ?_)
      have r10' : u'.gpr .r10 = BitVec.ofNat 64 j := by rw [g', r10]
      have r8' : u'.gpr .r8 = BitVec.ofNat 64 (n - 2 * 2 ^ w.log) := by rw [g', r8]
      refine WP.mono (step_ok h w hj hu' r10' r8') fun u'' ⟨r10'', r8'', cf'', hp⟩ => ?_
      by_cases he : n - 2 * 2 ^ w.log < j + 2 * 2 ^ w.log
      · left
        exact ⟨by simp only [eval, cf'', he, decide_true, Option.map_some, Bool.not_true],
          max (max (2 ^ w.log) j) (j + 2 * 2 ^ w.log), by omega, by omega, hp⟩
      · right
        refine ⟨by simp only [eval, cf'', he, decide_false, Option.map_some, Bool.not_false],
          n - (j + 2 * 2 ^ w.log), by omega, j + 2 * 2 ^ w.log, rfl, by omega, r10'', r8'', ?_⟩
        rw [show max (2 ^ w.log) (j + 2 * 2 ^ w.log) = max (max (2 ^ w.log) j) (j + 2 * 2 ^ w.log) by omega]
        exact hp
  -- The last `2 c` bytes.
  have hC : t₃.gpr .rcx = BitVec.ofNat 64 n := by rw [ht₃.2.1 .rcx (by decide) (by decide) (by decide), h.rcx]
  refine WP.mono (quadAt_ok h w ht₃ hi₂ hC (a := n - 2 * 2 ^ w.log) (by omega) hi₁ (by omega)) fun u ⟨hu, _⟩ => ?_
  rwa [show max i (n - 2 * 2 ^ w.log + 2 * 2 ^ w.log) = n by omega] at hu

/-- `copyBytes w`: the `n` bytes at `S` copied to `D`. -/
theorem copyBytes_ok (w : Width) : WP isa (copyBytes w) s (CopyPost s S D n) := by
  have hc : 2 * 2 ^ w.log < 2 ^ 31 := by have := log_le w; omega
  refine WP.seq (WP.mono (cmpRcx_ok h hc ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun u ⟨cf, hu⟩ => ?_)
  refine WP.seq (WP.mono (Q := CopyPost s S D n)
    (WP.ite (decide (n < 2 * 2 ^ w.log)) (by simp only [eval, cf])
      (fun hb => ladder_ok h w (of_decide_eq_true hb) hu)
      (fun hb => big_ok h w (by have := of_decide_eq_false hb; omega) hu)) fun v hv => ?_)
  cases w with
  | x16 => exact WP.block_nil hv
  | y32 => exact WP.of_runBlock ⟨_, rfl, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2⟩
  | z64 => exact WP.of_runBlock ⟨_, rfl, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2⟩

end

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
