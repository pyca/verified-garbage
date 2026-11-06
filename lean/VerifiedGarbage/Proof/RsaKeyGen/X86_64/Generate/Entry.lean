module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Generate
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Data
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Frame
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.X86_64.WordIOBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The controller's entry: its frame's words from the arguments and the state -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (limitOf)

/-! ## Whether the exponent is 3 -/

/-- The exponent's eight octets, most significant first, read as a word, are
`3 · 2^56` exactly when the exponent is 3. -/
theorem word_eq_three (m : Mem) (a : Addr) :
    m.readW a 64 = 0x0300000000000000 ↔ Spec.Rsa.os2ip (Spec.Rsa.bytesAt m a 8) = 3 := by
  have hb : ∀ j < 8, (m.readW a 64).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
    intro j hj
    rw [← Mem.extractLsb'_read m a (n := 8) hj]
    rfl
  have hc : ∀ j < 8, (0x0300000000000000 : BitVec 64).extractLsb' (8 * j) 8 = if j = 7 then 3 else 0 := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      h | h | h | h | h | h | h | h <;> subst h <;> decide
  rw [show Spec.Rsa.bytesAt m a 8 = Spec.Rsa.bytesAt m a 7 ++ [m (a + BitVec.ofNat 64 7)] from
    SearchInit.bytesAt_succ m a 7, SearchInit.os2ip_eq_three, SearchInit.or_eq_zero,
    SearchInit.orOf_eq_zero]
  have hx : (m (a + BitVec.ofNat 64 7)).setWidth 64 ^^^ 3 = 0 ↔ m (a + BitVec.ofNat 64 7) = 3 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp h)
      rw [BitVec.toNat_setWidth, show (3 : BitVec 64).toNat = 3 from rfl] at this
      apply BitVec.eq_of_toNat_eq
      have hl := (m (a + BitVec.ofNat 64 7)).isLt
      rw [show (3 : BitVec 8).toNat = 3 from rfl]
      omega
    · intro h; rw [h]; decide
  rw [hx]
  constructor
  · intro h
    refine ⟨fun b hm => ?_, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
      have hj := List.mem_range.mp hj
      have := (hb j (by omega)).symm.trans ((congrArg (fun x : BitVec 64 => x.extractLsb' (8 * j) 8) h).trans
        (hc j (by omega)))
      rw [ite_eq_right (by omega)] at this
      exact this
    · have := (hb 7 (by decide)).symm.trans ((congrArg (fun x : BitVec 64 => x.extractLsb' (8 * 7) 8) h).trans
        (hc 7 (by decide)))
      exact this
  · rintro ⟨h0, h7⟩
    apply Proof.Bignum.X86_64.WordIO.eq_of_bytes
    intro j hj
    rw [hb j hj, hc j hj]
    by_cases h : j = 7
    · subst h; rw [ite_eq_left rfl]; exact h7
    · rw [ite_eq_right h]
      exact h0 _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)

/-! ## Where the buffers are -/

namespace GenInput

variable {p : GenPublic} {s : State}

theorem nowrap (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    r.base.toNat + r.len ≤ 2 ^ 64 := h.1.2.2.2.2.1 r hr

theorem write_disjoint (h : GenInput p s) {w r : Region} (hw : w ∈ inWrites s) (hr : r ∈ inReads s) :
    w.Disjoint r := h.1.2.2.2.2.2.2.1 w hw r hr

theorem stack_disjoint (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s ++ inReads s) :
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r ∧ (below (s.gpr .rsp) stackUse).Disjoint r :=
  h.1.2.2.2.2.2.2.2.1 r hr

theorem writes_pairwise (h : GenInput p s) : (inWrites s).Pairwise Region.Disjoint :=
  h.1.2.2.2.2.2.1

theorem sp_eq (h : GenInput p s) : p.sp = s.gpr .rsp := by rw [← h.2]; rfl

theorem room (h : GenInput p s) : stackUse ≤ p.sp.toNat := by rw [h.sp_eq]; exact h.1.2.1

theorem top (h : GenInput p s) : p.sp.toNat + 24 ≤ 2 ^ 64 := by rw [h.sp_eq]; exact h.1.1

theorem F_toNat (h : GenInput p s) : p.F.toNat = p.sp.toNat - 160 := by
  have : 552 ≤ p.sp.toNat := h.room
  have h160 : (BitVec.ofNat 64 160).toNat = 160 := rfl
  rw [GenPublic.F, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h160]; omega), h160]

/-- The frame is working space once allocated. -/
theorem frame_scr (h : GenInput p s) {t : State} (hw : t.wr = p.frame :: s.wr) : Scr t p.F 160 := by
  refine Scr.of_mem (by rw [hw]; exact List.mem_cons_self ..) ?_
  have := h.F_toNat
  have : 552 ≤ p.sp.toNat := h.room
  have := h.top
  omega

/-- The regions the controller (and its callees) may write, and its stack. -/
def changes (s : State) : List Region := inWrites s ++ [below (s.gpr .rsp) stackUse]

theorem read_disjoint (h : GenInput p s) {r : Region} (hr : r ∈ inReads s) :
    ∀ w ∈ changes s, r.Disjoint w := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (h.write_disjoint hw hr).symm
  · obtain rfl := List.mem_singleton.mp hw
    exact (h.stack_disjoint (List.mem_append_right _ hr)).2.symm

theorem bytes_frame (h : GenInput p s) {r : Region} (hr : r ∈ inReads s) {m m' : Mem}
    (hf : Frame (changes s) m m') : Spec.Rsa.bytesAt m' r.base r.len = Spec.Rsa.bytesAt m r.base r.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hn := h.nowrap (List.mem_append_right _ hr)
  exact hf.bytes (h.read_disjoint hr) (by omega) (List.mem_range.mp hi)

theorem random_frame (h : GenInput p s) {m m' : Mem} (hf : Frame (changes s) m m') :
    Spec.Rsa.bytesAt m' p.rp p.randLen = Spec.Rsa.bytesAt m p.rp p.randLen := by
  rw [← h.2]
  exact h.bytes_frame (r := inRand s) (by simp [inReads]) hf

/-- The frame is in the stack the controller may use. -/
theorem frame_sub (h : GenInput p s) : Region.Sub p.frame (below (s.gpr .rsp) stackUse) := by
  rw [← h.sp_eq]
  exact Offset.sub_below p.sp (by decide) (by decide)

theorem frame_disjoint_writes (h : GenInput p s) {r : Region} (hr : r ∈ inWrites s) : p.frame.Disjoint r :=
  fun x hx hy => (h.stack_disjoint (List.mem_append_left _ hr)).2 x (h.frame_sub x hx) hy

end GenInput

/-! ## The entry's stores -/

def regValues (s : State) : List (Nat × BitVec 64) :=
  [(9, s.gpr .r12), (0, s.gpr .rdi), (2, s.gpr .rdx), (3, s.gpr .rcx), (4, s.gpr .r8), (5, s.gpr .r9)]

def argValues (s : State) : List (Nat × BitVec 64) := [(6, stackArg s 0), (7, stackArg s 1)]

def headValues (s : State) : List (Nat × BitVec 64) := regValues s ++ argValues s

/-- The counted candidates of a prime's search, from the primes' octets `w`
and the exponent's word `ew`. -/
def limitBV (w ew : BitVec 64) : BitVec 64 :=
  if ew = 0x0300000000000000 then w <<< 6 else (w <<< 3) <<< 2 + w <<< 3

def wordValues (s : State) : List (Nat × BitVec 64) :=
  [(1, s.mem.readW (stackArg s 1 + 8) 64), (8, 0),
    (11, limitBV (s.mem.readW (stackArg s 1 + 8) 64) (s.mem.readW (stackArg s 1 + 48) 64))]

def entryValues (s : State) : List (Nat × BitVec 64) := headValues s ++ wordValues s

theorem entryValues_bound (s : State) : ∀ e ∈ entryValues s, e.1 < 20 := by
  simp only [entryValues, headValues, regValues, argValues, wordValues, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem arg_contains (s : State) {j : Nat} (hj : j < 2) :
    (inArgs s).Contains (stackArgAddr s j) 8 := by
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
    congr 2
    omega]
  exact Offset.contains_base _ (by omega) (by omega)

theorem input_args {p : GenPublic} {s : State} (h : GenInput p s) :
    ∀ j < 2, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8 := by
  intro j hj
  refine ⟨inArgs s, ?_, arg_contains s hj⟩
  rw [h.1.2.2.1]
  exact List.mem_append_left _ (by simp [inReads])

/-- The frame's stores keep what is outside it. -/
theorem entry_frame {p : GenPublic} {s : State} (h : GenInput p s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) {r : Region} (hr : r ∈ inWrites s ++ inReads s) {a : Addr} {n : Nat}
    (ha : r.Contains a (n / 8)) (hn : n / 8 < 2 ^ 64) :
    (writeFrame s.mem p.F values).readW a n = s.mem.readW a n := by
  refine (writeFrame_frame s.mem p.F values hb).readW ha (fun q hq => ?_) hn
  obtain rfl := List.mem_singleton.mp hq
  exact fun x hx hy => (h.stack_disjoint hr).2 x (h.frame_sub x hy) hx

theorem alloc_rsp {p : GenPublic} {s : State} (h : GenInput p s) :
    (allocated 160 s).gpr .rsp = p.F := by
  rw [allocated_rsp, ← h.sp_eq]

theorem alloc_wr {p : GenPublic} {s : State} (h : GenInput p s) :
    (allocated 160 s).wr = p.frame :: s.wr := by
  show (⟨s.gpr .rsp - BitVec.ofNat 64 160, 160⟩ : Region) :: s.wr = _
  rw [← h.sp_eq]

theorem arg_addr {p : GenPublic} {s : State} (h : GenInput p s) (k : Nat) :
    p.F + BitVec.ofNat 64 (168 + 8 * k) = stackArgAddr s k := by
  rw [show 168 + 8 * k = 160 + 8 * (k + 1) by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.sub_add_cancel, h.sp_eq]
  rfl

theorem arg_read {p : GenPublic} {s : State} (h : GenInput p s) (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 20) {k : Nat} (hk : k < 2) :
    (writeFrame s.mem p.F values).readW (p.F + BitVec.ofNat 64 (168 + 8 * k)) 64 = stackArg s k := by
  rw [arg_addr h]
  exact entry_frame h values hb (r := inArgs s) (by simp [inReads]) (arg_contains s hk) (by decide)

theorem arg_in {p : GenPublic} {s : State} (h : GenInput p s) {t : State} (hr : t.rd = s.rd)
    (hw : t.wr = p.frame :: s.wr) {k : Nat} (hk : k < 2) :
    InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 (168 + 8 * k)) 8 := by
  rw [arg_addr h, hr, hw]
  obtain ⟨r, hr', hc⟩ := input_args h k hk
  refine ⟨r, ?_, hc⟩
  rcases List.mem_append.mp hr' with hm | hm
  · exact List.mem_append_left _ hm
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)

theorem entryHead_split : entryHead =
    ([.store { base := .rsp, disp := 72 } .r12, .mov .r12 (.reg .rsp),
      .store (field 0) .rdi, .store (field 2) .rdx, .store (field 3) .rcx, .store (field 4) .r8,
      .store (field 5) .r9] : List Instr) ++
    ([.mov .rax (.mem (callerArg 0)), .store (field 6) .rax,
      .mov .rax (.mem (callerArg 1)), .store (field 7) .rax] : List Instr) := rfl

theorem entry_regs_ok {p : GenPublic} {s : State} (h : GenInput p s) :
    WP isa (.block [.store { base := .rsp, disp := 72 } .r12, .mov .r12 (.reg .rsp),
      .store (field 0) .rdi, .store (field 2) .rdx, .store (field 3) .rcx, .store (field 4) .r8,
      .store (field 5) .r9]) (allocated 160 s) fun t =>
      (t.gpr .r12 = p.F ∧ t.mem = writeFrame s.mem p.F (regValues s)) ∧ Keep [.r12] (allocated 160 s) t := by
  have scr := h.frame_scr (alloc_wr h)
  have hs : ∀ d, d + 8 ≤ 160 → InRegions (allocated 160 s).wr (p.F + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hs0 : InRegions (allocated 160 s).wr p.F 8 := by simpa only [BitVec.add_zero] using hs 0 (by decide)
  have hsp := alloc_rsp h
  refine WP.keep [.r12] ?_ rfl
  unfold writeFrame regValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero, hsp,
    allocated_reg _ _ _ (show Reg.r12 ≠ .rsp by decide), allocated_reg _ _ _ (show Reg.rdi ≠ .rsp by decide),
    allocated_reg _ _ _ (show Reg.rdx ≠ .rsp by decide), allocated_reg _ _ _ (show Reg.rcx ≠ .rsp by decide),
    allocated_reg _ _ _ (show Reg.r8 ≠ .rsp by decide), allocated_reg _ _ _ (show Reg.r9 ≠ .rsp by decide),
    allocated_mem, hs0, hs 16 (by decide), hs 24 (by decide), hs 32 (by decide), hs 40 (by decide),
    hs 72 (by decide)]

theorem entry_args_ok {p : GenPublic} {s t : State} (h : GenInput p s)
    (hm : t.mem = writeFrame s.mem p.F (regValues s)) (k : Keep [.r12] (allocated 160 s) t)
    (hr : t.gpr .r12 = p.F) :
    WP isa (.block [.mov .rax (.mem (callerArg 0)), .store (field 6) .rax,
      .mov .rax (.mem (callerArg 1)), .store (field 7) .rax]) t fun u =>
      (u.gpr .rax = stackArg s 1 ∧ u.mem = writeFrame t.mem p.F (argValues s)) ∧ Keep [.rax] t u := by
  have hb : ∀ e ∈ regValues s, e.1 < 20 := fun e he =>
    entryValues_bound s e (List.mem_append_left _ (List.mem_append_left _ he))
  have htr : t.rd = s.rd := k.2.1
  have htw : t.wr = p.frame :: s.wr := k.2.2.trans (alloc_wr h)
  have hsp : t.gpr .rsp = p.F := (k.gpr (by decide)).trans (alloc_rsp h)
  have scr := h.frame_scr htw
  have hs : ∀ d, d + 8 ≤ 160 → InRegions t.wr (p.F + BitVec.ofNat 64 d) 8 := fun _ hd => scr.st hd
  have hv0 : t.mem.readW (p.F + BitVec.ofNat 64 168) 64 = stackArg s 0 := by
    rw [hm]; exact arg_read h _ hb (k := 0) (by decide)
  have hv1 : t.mem.readW (p.F + BitVec.ofNat 64 176) 64 = stackArg s 1 := by
    rw [hm]; exact arg_read h _ hb (k := 1) (by decide)
  have ha0 : InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 168) 8 := arg_in h htr htw (k := 0) (by decide)
  have ha1 : InRegions (t.rd ++ t.wr) (p.F + BitVec.ofNat 64 176) 8 := arg_in h htr htw (k := 1) (by decide)
  refine WP.keep [.rax] ?_ rfl
  unfold writeFrame argValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, callerArg, frameBytes, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast,
    Nat.reduceMul, Nat.reduceAdd, hsp, hr, read_above_store, hv0, hv1, ha0, ha1,
    hs 48 (by decide), hs 56 (by decide)]

theorem entry_head_ok {p : GenPublic} {s : State} (h : GenInput p s) :
    WP isa (.block entryHead) (allocated 160 s) fun t =>
      t.gpr .r12 = p.F ∧ t.gpr .rax = stackArg s 1 ∧ t.mem = writeFrame s.mem p.F (headValues s) ∧
      Keep [.r12, .rax] (allocated 160 s) t := by
  rw [entryHead_split, WP.block_append_iff]
  refine WP.mono (entry_regs_ok h) fun t ⟨⟨hr, hm⟩, k⟩ => ?_
  refine WP.mono (entry_args_ok h hm k hr) fun u ⟨⟨ha, hu⟩, ku⟩ => ?_
  exact ⟨(ku.gpr (by decide)).trans hr, ha, by rw [hu, hm, headValues, writeFrame_append],
    (k.trans ku).mono (by decide)⟩

theorem bv_sub_beq (x y : BitVec 64) : (x - y == 0) = decide (x = y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg (· + y) h
    simp only [BitVec.sub_add_cancel] at this
    rw [this]; exact BitVec.zero_add _
  · intro h; rw [h, BitVec.sub_self]; rfl

theorem limitBV_eq {L : Nat} {ew : BitVec 64} {eB : List Byte} (hL : L ≤ 512)
    (he : ew = 0x0300000000000000 ↔ Spec.Rsa.os2ip eB = 3) :
    limitBV (BitVec.ofNat 64 L) ew = BitVec.ofNat 64 (limitOf L eB) := by
  unfold limitBV limitOf primeLimit
  rw [SearchInit.shl_ofNat _ 6 (by omega), SearchInit.shl_ofNat _ 3 (by omega),
    SearchInit.shl_ofNat _ 2 (by omega), SearchInit.add_ofNat]
  by_cases h : ew = 0x0300000000000000
  · rw [ite_eq_left h, ite_eq_left (he.mp h)]; congr 1; omega
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (he.mpr h'))]; congr 1; omega

theorem entry_words_ok {p : GenPublic} {s u : State} (h : GenInput p s)
    (hm : u.mem = writeFrame s.mem p.F (headValues s))
    (hra : u.gpr .rax = stackArg s 1) (hr : u.gpr .r12 = p.F)
    (huw : u.wr = p.frame :: s.wr) :
    WP isa (.block entryWords) u fun t =>
      t.mem = writeFrame u.mem p.F (wordValues s) ∧ Keep [.rcx, .rdx, .r8, .r9, .r11] u t := by
  have hb : ∀ e ∈ headValues s, e.1 < 20 := fun e he =>
    entryValues_bound s e (List.mem_append_left _ he)
  have scr := h.frame_scr huw
  have hs : ∀ d, d + 8 ≤ 160 → InRegions u.wr (p.F + BitVec.ofNat 64 d) 8 := fun _ hd => scr.st hd
  have hst (d : Nat) (hd : d + 8 ≤ 56) : (inState s).Contains (stackArg s 1 + BitVec.ofNat 64 d) 8 :=
    Offset.contains_base _ hd (by omega)
  have hv (d : Nat) (hd : d + 8 ≤ 56) :
      u.mem.readW (stackArg s 1 + BitVec.ofNat 64 d) 64 = s.mem.readW (stackArg s 1 + BitVec.ofNat 64 d) 64 := by
    rw [hm]
    exact entry_frame h _ hb (r := inState s) (by simp [inWrites]) (hst d hd) (by decide)
  have ha (d : Nat) (hd : d + 8 ≤ 56) : InRegions (u.rd ++ u.wr) (stackArg s 1 + BitVec.ofNat 64 d) 8 := by
    refine ⟨inState s, ?_, hst d hd⟩
    rw [huw, h.1.2.2.2.1]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (by simp [inWrites]))
  have hv8 := hv 8 (by decide)
  have hv48 := hv 48 (by decide)
  have ha8 := ha 8 (by decide)
  have ha48 := ha 48 (by decide)
  refine WP.keep [.rcx, .rdx, .r8, .r9, .r11] ?_ rfl
  unfold entryWords writeFrame wordValues limitBV
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases he : s.mem.readW (stackArg s 1 + BitVec.ofNat 64 48) 64 = 0x0300000000000000 <;>
  xrun [State.ea, field, stw, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    hra, hr, hv8, hv48, ha8, ha48, eval, execCmov, bv_sub_beq, he,
    hs 8 (by decide), hs 64 (by decide), hs 88 (by decide)] <;>
  split <;> rename_i hc <;> first | rfl | exact absurd hc he | exact absurd he hc

theorem entry_ok {p : GenPublic} {s : State} (h : GenInput p s) :
    WP isa (.block (entryHead ++ entryWords)) (allocated 160 s) fun t =>
      t.gpr .r12 = p.F ∧ t.mem = writeFrame s.mem p.F (entryValues s) ∧
      Keep [.r12, .rax, .rcx, .rdx, .r8, .r9, .r11] (allocated 160 s) t := by
  rw [WP.block_append_iff]
  refine WP.mono (entry_head_ok h) fun u ⟨hr, ha, hm, k⟩ => ?_
  have huw : u.wr = p.frame :: s.wr := k.2.2.trans (alloc_wr h)
  refine WP.mono (entry_words_ok h hm ha hr huw) fun t ⟨ht, kt⟩ =>
    ⟨(kt.gpr (by decide)).trans hr, ?_, (k.trans kt).mono (by decide)⟩
  rw [ht, hm, entryValues, writeFrame_append]

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

namespace GenInput

variable {p : GenPublic} {s : State}

theorem state_words (h : GenInput p s) {m : Mem} (hf : Frame [p.frame] s.mem m) (d : Nat) (hd : d + 8 ≤ 56) :
    m.readW (p.stp + BitVec.ofNat 64 d) 64 = s.mem.readW (p.stp + BitVec.ofNat 64 d) 64 := by
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  refine hf.readW (r := ⟨p.stp, 56⟩) (Offset.contains_base _ hd (by omega)) (fun q hq => ?_) (by decide)
  obtain rfl := List.mem_singleton.mp hq
  rw [← hst]
  exact (h.frame_disjoint_writes (by simp [inWrites])).symm

theorem state_bytes (h : GenInput p s) {m : Mem} (hf : Frame [p.frame] s.mem m) :
    Spec.Rsa.bytesAt m (p.stp + 48) 8 = Spec.Rsa.bytesAt s.mem (p.stp + 48) 8 := by
  have hst : inState s = ⟨p.stp, 56⟩ := by rw [← h.2]; rfl
  have hn := h.nowrap (r := inState s) (by simp [inWrites])
  rw [hst] at hn
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine hf.bytes (R := ⟨p.stp + 48, 8⟩) (fun q hq => ?_) (by show 8 ≤ 2 ^ 64; decide) hi
  obtain rfl := List.mem_singleton.mp hq
  have hd := h.frame_disjoint_writes (r := inState s) (by simp [inWrites])
  rw [hst] at hd
  exact (hd.symm.sub_left (Offset.sub_base _ (by omega) (n := 8) (d := 48) (k := 56))) |>.symm.symm

end GenInput

/-- The state's words for the progress on entry. -/
theorem stateOk_entry {p : GenPublic} {s : State} (h : GenInput p s) {m : Mem} (hf : Frame [p.frame] s.mem m) :
    StateOk p (genProgress s) m := by
  have hw (d : Nat) (hd : d + 8 ≤ 56) := h.state_words hf d hd
  have hpre := h.1
  obtain ⟨-, -, -, -, -, -, -, -, hL, -, -, hrem, hcap, hph, -⟩ := hpre
  have hstp : p.stp = stackArg s 1 := by rw [← h.2]; rfl
  have hLp : p.L = genLen s := by rw [← h.2]; rfl
  have heB : p.eB = genE s := by rw [← h.2]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, BitVec.isLt _⟩
  · change m.readW (p.stp + BitVec.ofNat 64 0) 64 = _
    rw [hw 0 (by decide), BitVec.add_zero, hstp]; exact (ofNat_toNat64 _).symm
  · change m.readW (p.stp + BitVec.ofNat 64 8) 64 = _
    rw [hw 8 (by decide), hLp, hstp, ofNat_toNat64]; rfl
  · change m.readW (p.stp + BitVec.ofNat 64 16) 64 = _
    rw [hw 16 (by decide), hLp, hstp]; exact hcap
  · change m.readW (p.stp + BitVec.ofNat 64 32) 64 = _
    rw [hw 32 (by decide), hstp]
    simp only [genProgress, keyProgressAt]
    have hph' : (s.mem.readW (stackArg s 1 + BitVec.ofNat 64 32) 64).toNat ≤ 1 := hph
    split
    · rename_i h0
      have h0' : (s.mem.readW (stackArg s 1 + BitVec.ofNat 64 32) 64).toNat = 0 := h0
      apply BitVec.eq_of_toNat_eq
      rw [h0']; rfl
    · rename_i h0
      have h0' : ¬(s.mem.readW (stackArg s 1 + BitVec.ofNat 64 32) 64).toNat = 0 := h0
      apply BitVec.eq_of_toNat_eq
      have : (s.mem.readW (stackArg s 1 + BitVec.ofNat 64 32) 64).toNat = 1 := by omega
      rw [this]; rfl
  · change m.readW (p.stp + BitVec.ofNat 64 40) 64 = _
    rw [hw 40 (by decide), hstp]; exact (ofNat_toNat64 _).symm
  · rw [h.state_bytes hf, heB, hstp]
  · rw [hLp, heB]
    exact hrem

/-- The controller's state on leaving its entry, before it clears the key's
buffer. -/
theorem gen_start {p : GenPublic} {s : State} (h : GenInput p s) :
    WP isa (.block (entryHead ++ entryWords)) (allocated 160 s) fun t =>
      GenFrame p s 0 (genProgress s) t ∧ Frame [p.frame] s.mem t.mem := by
  refine WP.mono (entry_ok h) fun t ⟨hr, hm, k⟩ => ?_
  have hb := entryValues_bound s
  have hw (j : Nat) (hj : j < 20) : word t.mem p.F (8 * j) = frameValue (entryValues s) j (word s.mem p.F (8 * j)) := by
    rw [hm]; exact writeFrame_word _ _ _ hb j hj
  have hfr : Frame [p.frame] s.mem t.mem := by rw [hm]; exact writeFrame_frame s.mem p.F _ hb
  have hf : Frame (GenInput.changes s) s.mem t.mem := by
    apply hfr.sub
    intro region hregion
    obtain rfl := List.mem_singleton.mp hregion
    exact ⟨_, by simp [GenInput.changes], h.frame_sub⟩
  have hL : p.L ≤ 512 := by rw [← h.2]; exact h.1.2.2.2.2.2.2.2.2.1.2.1
  have hstp : p.stp = stackArg s 1 := by rw [← h.2]; rfl
  refine ⟨⟨h, Nat.zero_le _, k.2.1, k.2.2.trans (alloc_wr h), (k.gpr (by decide)).trans (alloc_rsp h), hr,
    fun r hr hn hs => ?_, ?_, ?_, ?_, stateOk_entry h hfr⟩, hfr⟩
  · rw [k.gpr (by revert r; decide), allocated_reg _ _ _ hs]
  · change word t.mem p.F (8 * 9) = _
    rw [hw 9 (by decide)]
    rfl
  · rw [h.random_frame hf]; rw [← h.2]; rfl
  · intro e he
    rw [hw e.1 (GenPublic.headers_bound _ _ e he)]
    have hLs : genLen s = p.L := by rw [← h.2]; rfl
    have hlim : limitBV (s.mem.readW (stackArg s 1 + 8) 64) (s.mem.readW (stackArg s 1 + 48) 64) =
        BitVec.ofNat 64 (limitOf p.L p.eB) := by
      rw [show s.mem.readW (stackArg s 1 + 8) 64 = BitVec.ofNat 64 p.L by rw [← hLs]; exact (ofNat_toNat64 _).symm]
      exact limitBV_eq hL (by rw [word_eq_three]; rw [← h.2]; rfl)
    rw [← h.2] at he hlim
    simp only [GenPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [frameValue, entryValues, headValues, regValues, argValues, wordValues, List.cons_append,
        List.nil_append, List.foldl_cons, List.foldl_nil, genOfState, genLen, ofNat_toNat64, hlim,
        Nat.mul_div_cancel _ (show 0 < 8 by decide)] <;>
      rfl

end VG.Proof.RsaKeyGen.X86_64.Generate
