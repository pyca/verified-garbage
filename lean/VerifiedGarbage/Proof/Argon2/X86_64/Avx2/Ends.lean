import VerifiedGarbage.Proof.Argon2.X86_64.Avx2.Rows
import VerifiedGarbage.Proof.Argon2.X86_64.Finish

/-!
# Argon2 on x86-64 with AVX2: the first and last XOR

`initChunk k` copies 32 bytes of X XOR Y to both halves of scratch, and
`finishChunk k` writes 32 bytes of the permuted block XOR R to `out`; each
is proven for any prefix of the 32 chunks (`init_prefix`, `finish_prefix`).
-/

namespace VG.Proof.Argon2.X86_64.Avx2

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64 (at_)
open VG.Impl.Argon2.X86_64.Avx2
open VG.Proof.Argon2.X86_64 (off word working working_get Scratch ea_at Inputs blockAt_get
  xorBlock_get input_read input_unchanged Written scratch_unchanged)
open VG.Proof.Poly1305.X86_64.Avx2 (qw qword256_ymm qw_vbin qw_lane)

/-- A word at `p + d` after 32 bytes are written at `p + e`. -/
theorem read_write256 (m : Mem) (p : Addr) {d e : Nat} (hd : d + 8 ≤ 4096) (he : e + 32 ≤ 4096)
    (h8 : d % 8 = 0) (he8 : e % 8 = 0) (v : BitVec 256) :
    (m.writeW (off p e) v).readW (off p d) 64 =
      if e ≤ d ∧ d < e + 32 then qword256 v ((d - e) / 8) else m.readW (off p d) 64 := by
  split
  · rename_i h
    rw [show off p d = off p e + BitVec.ofNat 64 (8 * ((d - e) / 8)) from
      (Offset.add_add_eq p (by omega)).symm]
    refine (readW_writeW_inside _ _ v (k := 8 * ((d - e) / 8)) (n := 8) (by omega) (by decide)).trans ?_
    rw [qword256, show 8 * (8 * ((d - e) / 8)) = 64 * ((d - e) / 8) by omega]
  · exact readW_writeW_off m p v (n := 8) (by omega) (by omega) (by omega)

/-- The chunks `k < n` of both halves of scratch hold `r`. -/
def Initialized (m : Mem) (p : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val / 4 < n → m.readW (off p (8 * i.val)) 64 = r[i] ∧ word m p i.val = r[i]

theorem qw_xor_ymm (s : State) (k : Nat) (hk : k < 4) :
    qword256 (((VOp.vbin .vpxor .l256 x0 x0 x1).exec s).ymm x0) k = qw s x0 k ^^^ qw s x1 k := by
  rw [qword256_ymm _ _ hk]
  simp only [qw_vbin, VBinOp.sse, ite_true, qword_pxor, qw_lane]


theorem initChunk_eq (k : Nat) : initChunk k =
    [.vmovdquLoad .l256 x0 (at_ .rdi (32 * k)), .vmovdquLoad .l256 x1 (at_ .rsi (32 * k)),
      .vop (.vbin .vpxor .l256 x0 x0 x1), .vmovdquStore .l256 (at_ .rcx (32 * k)) x0,
      .vmovdquStore .l256 (at_ .rcx (1024 + 32 * k)) x0] := rfl

/-- The 32 bytes `initChunk k` writes, quadword by quadword. -/
def XorChunk (s : State) (x y : Addr) (k : Nat) (v : BitVec 256) : Prop :=
  ∀ q < 4, qword256 v q = s.mem.readW (off x (32 * k + 8 * q)) 64 ^^^ s.mem.readW (off y (32 * k + 8 * q)) 64

theorem initChunk_ok {k : Nat} (hk : k < 32) {s : State} {p x y : Addr} (hs : Scratch s p)
    (hin : Inputs s x y p) :
    WP isa (.block (initChunk k)) s fun t => ∃ v, XorChunk s x y k v ∧
      t.mem = (s.mem.writeW (off p (32 * k)) v).writeW (off p (1024 + 32 * k)) v ∧ VKeep s t ∧
      (Masks s → Masks t) := by
  have lx : InRegions (s.rd ++ s.wr) (off x (32 * k)) 32 :=
    ⟨_, hin.xread, Offset.contains_base x (by omega) (by omega)⟩
  have ly : InRegions (s.rd ++ s.wr) (off y (32 * k)) 32 :=
    ⟨_, hin.yread, Offset.contains_base y (by omega) (by omega)⟩
  have w1 := hs.write (d := 32 * k) (n := 32) (by omega)
  have w2 := hs.write (d := 1024 + 32 * k) (n := 32) (by omega)
  apply WP.of_runBlock
  simp only [initChunk_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load256,
    State.store256_eq, ea_at, State.setV_rd, State.setV_wr, State.setV_gpr, State.setV_mem,
    VOp.exec_gpr, VOp.exec_mem, VOp.exec_wr, State.setMem_wr, State.setMem_gpr,
    ymm_setMem, hs.reg, hin.xreg, hin.yreg, lx, ly, w1, w2, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨_, fun q hq => ?_, rfl, ?_, fun h => ?_⟩
  · simp only [qw_xor_ymm _ _ hq, qw_set256 _ _ _ _ hq, ↓reduceIte, reduceCtorEq,
      qword256_readW _ _ hq, Offset.add_add]
  · exact ⟨by simp only [State.setMem_gpr, VOp.exec_gpr, State.setV_gpr],
      by simp only [State.setMem_rd, VOp.exec_rd, State.setV_rd],
      by simp only [State.setMem_wr, VOp.exec_wr, State.setV_wr],
      by simp only [State.setMem_mxcsr, VG.Proof.Argon2.X86_64.Avx2.VOp.exec_mxcsr, State.setV_mxcsr]⟩
  · exact ((((h.setV (by decide) (by decide)).setV (by decide) (by decide)).vbin (by decide)
      (by decide)).setMem _).setMem _


theorem ifp {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem ifn {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

theorem initialized_step {m : Mem} {p : Addr} {r : Block} {n : Nat} (hn : n < 32)
    (h : Initialized m p r n) {v : BitVec 256} (hv : ∀ q < 4, ∀ hi : 4 * n + q < 128,
      qword256 v q = r[4 * n + q]'hi) :
    Initialized ((m.writeW (off p (32 * n)) v).writeW (off p (1024 + 32 * n)) v) p r (n + 1) := by
  intro i hi
  have hi' := i.isLt
  simp only [word]
  rw [read_write256 _ p (by omega) (by omega) (by omega) (by omega),
    read_write256 _ p (by omega) (by omega) (by omega) (by omega),
    read_write256 _ p (by omega) (by omega) (by omega) (by omega),
    read_write256 _ p (by omega) (by omega) (by omega) (by omega)]
  by_cases e : i.val / 4 = n
  · have q := hv (i.val % 4) (Nat.mod_lt _ (by decide)) (by omega)
    simp only [show 4 * n + i.val % 4 = i.val by omega] at q
    simp (disch := omega) only [ifp, ifn, Fin.getElem_fin,
      show (8 * i.val - 32 * n) / 8 = i.val % 4 by omega,
      show (1024 + 8 * i.val - (1024 + 32 * n)) / 8 = i.val % 4 by omega, q, and_self]
  · have := h i (by omega)
    simp (disch := omega) only [ifn]
    exact this

theorem _root_.VG.Proof.Argon2.X86_64.Inputs.of_vkeep {s t : State} {x y p : Addr} (h : Inputs s x y p) (hk : VKeep s t) :
    Inputs t x y p :=
  ⟨by rw [hk.gpr]; exact h.xreg, by rw [hk.gpr]; exact h.yreg, by rw [hk.rd, hk.wr]; exact h.xread,
    by rw [hk.rd, hk.wr]; exact h.yread, h.xsep, h.ysep⟩

/-- Initialize the first `n` chunks, framing both input blocks. -/
theorem init_prefix (n : Nat) (hn : n ≤ 32) {s : State} {p x y : Addr} (hs : Scratch s p)
    (hin : Inputs s x y p) :
    WP isa (.block ((List.range n).flatMap initChunk)) s fun t =>
      Initialized t.mem p (xorBlock (blockAt s.mem x) (blockAt s.mem y)) n ∧
      Frame [⟨p, 4096⟩] s.mem t.mem ∧ VKeep s t ∧ (Masks s → Masks t) := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, VKeep.refl s, id⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk, hm⟩
    refine (initChunk_ok (by omega) (hs.of_vkeep hk) (hin.of_vkeep hk)).mono ?_
    rintro u ⟨v, hv, hmem, hk', hm'⟩
    refine ⟨?_, ?_, hk.trans hk', fun h => hm' (hm h)⟩
    · rw [hmem]
      refine initialized_step (by omega) ht fun q hq hi => ?_
      rw [hv q hq, show 32 * n + 8 * q = 8 * (4 * n + q) by omega,
        input_unchanged hf hin.xsep ⟨4 * n + q, hi⟩, input_unchanged hf hin.ysep ⟨4 * n + q, hi⟩]
      simp only [xorBlock, Vector.getElem_zipWith, blockAt, Vector.getElem_ofFn]
      rfl
    · rw [hmem]
      exact (hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base p (by omega) (by omega))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base p (by omega) (by omega))


theorem finishChunk_eq (k : Nat) : finishChunk k =
    [.vmovdquLoad .l256 x0 (at_ .rcx (1024 + 32 * k)), .vmovdquLoad .l256 x1 (at_ .rcx (32 * k)),
      .vop (.vbin .vpxor .l256 x0 x0 x1), .vmovdquStore .l256 (at_ .rdx (32 * k)) x0] := rfl

theorem finishChunk_ok {k : Nat} (hk : k < 32) {s : State} {p out : Addr} (hs : Scratch s p)
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr) :
    WP isa (.block (finishChunk k)) s fun t => ∃ v : BitVec 256,
      (∀ q < 4, qword256 v q = word s.mem p (4 * k + q) ^^^ s.mem.readW (off p (8 * (4 * k + q))) 64) ∧
      t.mem = s.mem.writeW (off out (32 * k)) v ∧ VKeep s t ∧ (Masks s → Masks t) := by
  have r1 := hs.read (d := 1024 + 32 * k) (n := 32) (by omega)
  have r2 := hs.read (d := 32 * k) (n := 32) (by omega)
  have w : InRegions s.wr (off out (32 * k)) 32 := ⟨_, hw, Offset.contains_base out (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [finishChunk_eq, runBlock_cons, runStep_some, runBlock_nil, exec, State.load256,
    State.store256_eq, ea_at, State.setV_rd, State.setV_wr, State.setV_gpr, State.setV_mem,
    VOp.exec_gpr, VOp.exec_mem, VOp.exec_wr, hs.reg, ho, r1, r2, w, ite_true, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨_, fun q hq => ?_, rfl, ?_, fun h => ?_⟩
  · simp only [qw_xor_ymm _ _ hq, qw_set256 _ _ _ _ hq, ↓reduceIte, reduceCtorEq,
      qword256_readW _ _ hq, Offset.add_add, word]
    rw [show 1024 + 32 * k + 8 * q = 1024 + 8 * (4 * k + q) by omega,
      show 32 * k + 8 * q = 8 * (4 * k + q) by omega]
  · exact ⟨by simp only [State.setMem_gpr, VOp.exec_gpr, State.setV_gpr],
      by simp only [State.setMem_rd, VOp.exec_rd, State.setV_rd],
      by simp only [State.setMem_wr, VOp.exec_wr, State.setV_wr],
      by simp only [State.setMem_mxcsr, VG.Proof.Argon2.X86_64.Avx2.VOp.exec_mxcsr, State.setV_mxcsr]⟩
  · exact (((h.setV (by decide) (by decide)).setV (by decide) (by decide)).vbin (by decide)
      (by decide)).setMem _

/-- Finish the first `n` chunks, preserving scratch. -/
theorem finish_prefix (n : Nat) (hn : n ≤ 32) {s : State} {p out : Addr} (hs : Scratch s p)
    (ho : s.gpr .rdx = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) :
    WP isa (.block ((List.range n).flatMap finishChunk)) s fun t =>
      (∀ i : Fin 128, i.val / 4 < n →
        t.mem.readW (off out (8 * i.val)) 64 = (xorBlock (working s.mem p) (blockAt s.mem p))[i]) ∧
      Frame [⟨out, 1024⟩] s.mem t.mem ∧ VKeep s t ∧ (Masks s → Masks t) := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, VKeep.refl s, id⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk, hm⟩
    refine (finishChunk_ok (out := out) (by omega) (hs.of_vkeep hk) (by rw [hk.gpr]; exact ho)
      (by rw [hk.wr]; exact hw)).mono ?_
    rintro u ⟨v, hv, hmem, hk', hm'⟩
    refine ⟨fun i hi => ?_, ?_, hk.trans hk', fun h => hm' (hm h)⟩
    · have hi' := i.isLt
      rw [hmem, read_write256 _ out (by omega) (by omega) (by omega) (by omega)]
      by_cases e : i.val / 4 = n
      · rw [ifp (by omega), show (8 * i.val - 32 * n) / 8 = i.val % 4 by omega,
          hv _ (Nat.mod_lt _ (by decide)), show 4 * n + i.val % 4 = i.val by omega, word,
          scratch_unchanged hf hd (d := 1024 + 8 * i.val) (by omega),
          scratch_unchanged hf hd (d := 8 * i.val) (by omega), xorBlock_get, working_get, blockAt_get]
      · rw [ifn (by omega)]
        exact ht i (by omega)
    · rw [hmem]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base out (by omega) (by omega))

end VG.Proof.Argon2.X86_64.Avx2
