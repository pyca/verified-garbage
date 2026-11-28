module

-- separate module: the helpers every proof of the trees (xmssTree, forsSign, the verification functions) shares

public import VerifiedGarbage.Proof.SlhDsa.AArch64.Contracts
public import VerifiedGarbage.Proof.Framework.AArch64.Steps
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on AArch64: what the proofs of the trees share

Generic facts the proofs of `xmssTree` and `forsSign` (and of the other
internal functions, which may import them) use:

* two runs, each with its own invariants (`relSeq`, `relLoop`), and a loop
  of one run (`wpLoop`); a block the taint analysis proves constant time
  from the registers `rs` (`taintR`);
* parts of `scratch`, 64 KiB at `S` (`in_scr`, `disj_scr`, `sub_scr`, …),
  and bytes a frame keeps (`bytesAt_frame`, `readW_frame`);
* `Env` across a frame that keeps the lanes' `PK.seed` and `a16`
  (`env_frame`), and that it fixes them (`env_unique`);
* weakest preconditions of the instructions the blocks use, one at a time,
  as `Framework/AArch64/Steps.lean` has them for others.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.TreeBase

open VG VG.AArch64 VG.AArch64.Steps
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)

/-! ## Two runs, each with its own invariants -/

/-- `c₁` then `c₂`, from states each satisfying a predicate of its own. -/
theorem relSeq {A₁ A₂ B₁ B₂ : State → Prop} {c₁ c₂ : Prog isa} {Q : State → State → Prop}
    (hct : RelCT isa (fun a b => A₁ a ∧ A₂ b) c₁ fun _ _ => True)
    (h₁ : ∀ a, A₁ a → WP isa c₁ a B₁) (h₂ : ∀ b, A₂ b → WP isa c₁ b B₂)
    (hr : RelCT isa (fun a b => B₁ a ∧ B₂ b) c₂ Q) : RelCT isa (fun a b => A₁ a ∧ A₂ b) (.seq c₁ c₂) Q :=
  RelCT.seq (RelCT.mono (RelCT.wp hct fun a b h => ⟨h₁ a h.1, h₂ b h.2⟩) (fun _ _ h => h) fun _ _ h => h.2) hr

/-- A loop whose runs each keep an invariant of their own, at the same
measure, the condition after each pass being a function `cont` of it. -/
theorem relLoop {body : Prog isa} {c : Cond} {I₁ I₂ : Nat → State → Prop} {Q₁ Q₂ : State → Prop}
    (cont : Nat → Bool) (g : Nat → Nat)
    (hct : ∀ m, RelCT isa (fun a b => I₁ m a ∧ I₂ m b) body fun _ _ => True)
    (h₁ : ∀ m s, I₁ m s → WP isa body s fun s' => isa.eval c s' = some (cont m) ∧
      (cont m = false → Q₁ s') ∧ (cont m = true → g m < m ∧ I₁ (g m) s'))
    (h₂ : ∀ m s, I₂ m s → WP isa body s fun s' => isa.eval c s' = some (cont m) ∧
      (cont m = false → Q₂ s') ∧ (cont m = true → g m < m ∧ I₂ (g m) s'))
    (n : Nat) : RelCT isa (fun a b => I₁ n a ∧ I₂ n b) (.loop body c) fun a b => Q₁ a ∧ Q₂ b :=
  RelCT.loop (fun m a b => I₁ m a ∧ I₂ m b) (fun m => RelCT.mono
    (RelCT.wp (hct m) fun a b h => ⟨h₁ m a h.1, h₂ m b h.2⟩) (fun _ _ h => h)
    fun a b ⟨_, ha, hb⟩ => ⟨by rw [ha.1, hb.1], fun hf => by
      rw [ha.1, Option.some.injEq] at hf; exact ⟨ha.2.1 hf, hb.2.1 hf⟩, fun ht => by
      rw [ha.1, Option.some.injEq] at ht; exact ⟨g m, (ha.2.2 ht).1, (ha.2.2 ht).2, (hb.2.2 ht).2⟩⟩) n

/-- The loop of such a run. -/
theorem wpLoop {body : Prog isa} {c : Cond} {I : Nat → State → Prop} {Q : State → Prop}
    (cont : Nat → Bool) (g : Nat → Nat)
    (h : ∀ m s, I m s → WP isa body s fun s' => isa.eval c s' = some (cont m) ∧
      (cont m = false → Q s') ∧ (cont m = true → g m < m ∧ I (g m) s'))
    (n : Nat) {s : State} (hs : I n s) : WP isa (.loop body c) s Q :=
  WP.loop (M := isa) I (fun m s hI => WP.mono (h m s hI) fun s' ⟨he, hq, hi⟩ => by
    cases hc : cont m
    · exact .inl ⟨by rw [he, hc], hq hc⟩
    · exact .inr ⟨by rw [he, hc], g m, (hi hc).1, (hi hc).2⟩) n s hs

/-- Code the taint analysis proves constant time from the stack pointer and
the registers `rs`. -/
theorem taintR {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun x y hp => ⟨(hr x y hp).1, fun r hm => (hr x y hp).2 r (Taint.mem_ofRegs.mp hm)⟩) h

/-! ## `scratch` -/

theorem scr0 (S : Addr) : S = S + BitVec.ofNat 64 0 := (BitVec.add_zero S).symm

theorem at_add (S : Addr) (a i : Nat) : at' S a + BitVec.ofNat 64 i = at' S (a + i) := by
  rw [at', at', BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `(S + o).toNat`, with no wrap. -/
theorem toNat_at {S : Addr} {o : Nat} (h : S.toNat + o < 2 ^ 64) : (at' S o).toNat = S.toNat + o := by
  rw [at', BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h]),
    Nat.mod_eq_of_lt (by omega_using [h])]

/-- A part of `scratch` is in it. -/
theorem sub_scr (S : Addr) {o l : Nat} (h : o + l ≤ 65536) : Region.Sub ⟨at' S o, l⟩ ⟨S, 65536⟩ :=
  Offset.sub_base S h

/-- Parts of `scratch` that do not overlap. -/
theorem disj_scr (S : Addr) {o l o' l' : Nat} (h : o + l ≤ o' ∨ o' + l' ≤ o) (h₁ : o + l ≤ 65536)
    (h₂ : o' + l' ≤ 65536) : Region.Disjoint ⟨at' S o, l⟩ ⟨at' S o', l'⟩ :=
  Offset.disjoint S h (by omega_using [h₁]) (by omega_using [h₂])

/-- `scratch` as a writable region. -/
theorem in_scr {wr : List Region} {S : Addr} (h : ⟨S, 65536⟩ ∈ wr) {o n : Nat} (ho : o + n ≤ 65536) :
    InRegions wr (S + BitVec.ofNat 64 o) n :=
  ⟨_, h, Offset.contains_base _ ho (by omega_using [ho])⟩

/-- `scratch` as a readable region. -/
theorem in_scr' {rd wr : List Region} {S : Addr} (h : ⟨S, 65536⟩ ∈ wr) {o n : Nat} (ho : o + n ≤ 65536) :
    InRegions (rd ++ wr) (S + BitVec.ofNat 64 o) n := by
  obtain ⟨r, hr, hc⟩ := in_scr (wr := wr) h ho
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- `scratch` is writable under the regions of a contract. -/
theorem regions_scr {s : State} {S : Addr} {rd : List Region} {out : Region} (h : Regions s S rd out) :
    (⟨S, 65536⟩ : Region) ∈ s.wr := by
  rw [h.wr_eq]; exact List.mem_cons_self

theorem regions_out {s : State} {S : Addr} {rd : List Region} {out : Region} (h : Regions s S rd out) :
    out ∈ s.wr := by
  rw [h.wr_eq]; exact List.mem_cons_of_mem _ List.mem_cons_self

/-! ## Bytes a frame keeps -/

theorem bytesAt_ext {m m' : Mem} {a a' : Addr} {n : Nat}
    (h : ∀ i < n, m' (a' + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) : bytesAt m' a' n = bytesAt m a n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- Bytes a frame does not meet are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' a n = bytesAt m a n :=
  bytesAt_ext fun _ hi => hf.bytes (R := ⟨a, n⟩) hd hn hi

/-- A word a frame does not meet is unchanged. -/
theorem readW_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {a : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 8⟩ r) : m'.readW a 64 = m.readW a 64 := by
  simp only [Mem.readW]
  rw [hf.read (r := ⟨a, 8⟩) (by simp [Region.Contains]) hd (by decide)]

/-- A byte a frame does not meet is unchanged. -/
theorem byte_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {a : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 1⟩ r) : m' a = m a :=
  hf _ fun r hr => hd r hr _ (by simp [Region.Contains])

/-- Byte `i` of `bytesAt`. -/
theorem getD_bytesAt (m : Mem) (a : Addr) {L i : Nat} (hi : i < L) :
    (bytesAt m a L).getD i 0 = m (a + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The `L` bytes at `a` are `l` if each is. -/
theorem bytesAt_eq {m : Mem} {a : Addr} {L : Nat} {l : List Byte} (hl : l.length = L)
    (h : ∀ i < L, m (a + BitVec.ofNat 64 i) = l.getD i 0) : bytesAt m a L = l :=
  Proof.SlhDsa.ext_getD (by simp [bytesAt, hl]) fun i hi => by
    simp only [bytesAt, List.length_map, List.length_range] at hi
    rw [getD_bytesAt _ _ hi, h i hi]

theorem bytesAt_length (m : Mem) (a : Addr) (n : Nat) : (bytesAt m a n).length = n := by
  simp [bytesAt]

/-! ## `Env` -/

theorem laneA_eq (k : Nat) : Layout.laneA k = 3136 + 128 * k := rfl
theorem laneB_eq (k : Nat) : Layout.laneB k = 3648 + 2208 * k := rfl

variable {p : Params}

/-- `Env` across a frame whose regions keep the lanes' `PK.seed` and `a16`. -/
theorem env_frame (hn32 : p.n ≤ 32) {m m' : Mem} {S : Addr} {pk a : List Byte} {rs : List Region}
    (he : Env p m S pk a) (hf : Frame rs m m')
    (hd : ∀ {o l : Nat}, Layout.oA ≤ o → o + l ≤ Layout.oN → ∀ r ∈ rs, Region.Disjoint ⟨at' S o, l⟩ r) :
    Env p m' S pk a := by
  have hA : ∀ k < 4, ∀ o l, o + l ≤ p.n + 16 →
      bytesAt m' (at' S (Layout.laneA k + o)) l = bytesAt m (at' S (Layout.laneA k + o)) l :=
    fun k hk o l h => bytesAt_frame hf (hd (by rw [laneA_eq]; simp only [Layout.oA]; omega)
      (by rw [laneA_eq]; simp only [Layout.oN]; omega)) (by omega)
  have hB : ∀ k < 4, ∀ o l, o + l ≤ p.n + 16 →
      bytesAt m' (at' S (Layout.laneB k + o)) l = bytesAt m (at' S (Layout.laneB k + o)) l :=
    fun k hk o l h => bytesAt_frame hf (hd (by rw [laneB_eq]; simp only [Layout.oA]; omega)
      (by rw [laneB_eq]; simp only [Layout.oN]; omega)) (by omega)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [← he.seedA k hk, ← Nat.add_zero (Layout.laneA k), hA k hk 0 p.n (by omega)]
  · rw [← he.seedB k hk, ← Nat.add_zero (Layout.laneB k), hB k hk 0 p.n (by omega)]
  · rw [← he.adrsA k hk, hA k hk p.n 16 (by omega)]
  · rw [← he.adrsB k hk, hB k hk p.n 16 (by omega)]

/-- `Env` fixes `PK.seed` and `a16`. -/
theorem env_unique {m : Mem} {S : Addr} {pk pk' a a' : List Byte} (h : Env p m S pk a)
    (h' : Env p m S pk' a') : pk = pk' ∧ a = a' :=
  ⟨(h.seedA 0 (by decide)).symm.trans (h'.seedA 0 (by decide)),
    (h.adrsA 0 (by decide)).symm.trans (h'.adrsA 0 (by decide))⟩

theorem env_a16 {m : Mem} {S : Addr} {pk a : List Byte} (h : Env p m S pk a) : a.length = 16 := by
  rw [← h.adrsA 0 (by decide), bytesAt_length]

theorem env_pk {m : Mem} {S : Addr} {pk a : List Byte} (h : Env p m S pk a) : pk.length = p.n := by
  rw [← h.seedA 0 (by decide), bytesAt_length]

/-! ## Instructions, one at a time

As `Framework/AArch64/Steps.lean`, with the vector registers kept too
(`Up.v`, `Mu.v`), which the calling convention preserves the low halves of. -/

/-- `s'` is `s` with register `d` set to `x` (the flags aside). -/
structure Up (s s' : State) (d : Reg) (x : BitVec 64) : Prop where
  gpr : s'.gpr d = x
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  v : s'.v = s.v

theorem Up.write (s : State) (d : Reg) (x : BitVec 64) : Up s (s.write .x d x) d x :=
  ⟨by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun _ h => RegUpd.gpr_write_of_ne _ _ _ h,
    RegUpd.sp_write _ _ _ _, RegUpd.mem_write _ _ _ _, RegUpd.rd_write _ _ _ _, RegUpd.wr_write _ _ _ _,
    RegUpd.v_write _ _ _ _⟩

/-- `s'` is `s` with memory `m` (the flags aside). -/
structure Mu (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  sp : s'.sp = s.sp
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  v : s'.v = s.v

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_up {i : Instr} {d : Reg} {x : BitVec 64} (h : exec i s = some (s.write .x d x))
    (k : ∀ s', Up s s' d x → WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.cons h (k _ (Up.write s d x))

theorem wp_mu {i : Instr} {m : Mem} (h : exec i s = some { s with mem := m })
    (k : ∀ s', Mu s s' m → WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.cons h (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- `mov d, n` (`add d, n, #0`). -/
theorem wp_mov {d n : Reg} (k : ∀ s', Up s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n 0 :: is)) s Q :=
  wp_up (by rw [exec_addImm_x (by decide)]; simp only [State.read, BitVec.setWidth_eq, BitVec.add_zero]) k

theorem wp_addi {d n : Reg} {imm : Nat} (hi : imm < 4096)
    (k : ∀ s', Up s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n imm :: is)) s Q :=
  wp_up (by rw [exec_addImm_x hi]; simp only [State.read, BitVec.setWidth_eq]) k

theorem wp_subi {d n : Reg} {imm : Nat} (hi : imm < 4096)
    (k : ∀ s', Up s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .x d n imm :: is)) s Q :=
  wp_up (by rw [exec_subImm_x hi]; simp only [State.read, BitVec.setWidth_eq]) k

theorem wp_addr {d n m : Reg} (k : ∀ s', Up s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  wp_up (by rw [exec_add]; simp only [State.read, BitVec.setWidth_eq]) k

theorem wp_subr {d n m : Reg} (k : ∀ s', Up s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub .x d n m :: is)) s Q :=
  wp_up (by simp only [reduceExec, State.read, BitVec.setWidth_eq]) k

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Up s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .x d n sh :: is)) s Q :=
  wp_up (by rw [exec_lsr_x h]; simp only [State.read, BitVec.setWidth_eq]) k

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Up s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  wp_up (by simp only [reduceExec, Size.bits, h, ite_true, State.read, BitVec.setWidth_eq]) k

theorem wp_and {d n m : Reg} (k : ∀ s', Up s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .x d n m :: is)) s Q :=
  wp_up (by rw [exec_logic]; simp only [State.read, BitVec.setWidth_eq]) k

theorem wp_orr {d n m : Reg} (k : ∀ s', Up s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .orr .x d n m :: is)) s Q :=
  wp_up (by rw [exec_logic]; simp only [State.read, BitVec.setWidth_eq]) k

theorem wp_eor {d n m : Reg} (k : ∀ s', Up s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  wp_up (by rw [exec_logic]; simp only [State.read, BitVec.setWidth_eq]) k

/-- `movz d, #imm` (no shift). -/
theorem wp_movz {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Up s s' d (imm.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 0 :: is)) s Q :=
  wp_up (by simp only [reduceExec, Size.bits, Nat.mul_zero, BitVec.shiftLeft_zero]; rfl) k

/-- `movk d, #imm, lsl #16hw`. -/
theorem wp_movk {d : Reg} {imm : BitVec 16} {hw : Nat} (h : 16 * hw < 64)
    (k : ∀ s', Up s s' d ((s.gpr d &&& ~~~((0xFFFF : BitVec 64) <<< (16 * hw))) ||| (imm.setWidth 64 <<< (16 * hw))) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.movk .x d imm hw :: is)) s Q :=
  wp_up (by simp only [reduceExec, Size.bits, h, ite_true, State.read, BitVec.setWidth_eq]) k

theorem wp_ldr {d n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 32768)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Up s s' d (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .x d n off :: is)) s Q := by
  subst ha; exact wp_up (exec_ldr_x ho hin) k

/-- `ldrb t, [n, #off]`. -/
theorem wp_ldrb {d n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Up s s' d ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb d n off :: is)) s Q := by
  subst ha
  refine WP.cons ?_ (k _ (Up.write s d _))
  simp only [reduceExec, addr, Nat.mod_one, Nat.mul_one, ho, and_self, ite_true, Option.bind_some, State.load,
    hin, Option.map_some, Option.some.injEq]
  simp only [State.write, Size.bits]
  congr 2; funext r; split <;> try rfl
  simp only [Mem.read]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_append, BitVec.toNat_setWidth]

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 32768)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mu s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .x t n off :: is)) s Q := by
  subst ha; exact wp_mu (exec_str_x ho hout) k

/-- `strb t, [n, #off]`: the low byte of `t`. -/
theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mu s s' (s.mem.write a 1 ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  subst ha
  refine wp_mu ?_ k
  simp only [reduceExec, addr, Nat.mod_one, Nat.mul_one, ho, and_self, ite_true, Option.bind_some, State.store,
    hout, State.read, Size.bits, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), Nat.mul_one]

end

end VG.Proof.SlhDsa.AArch64.TreeBase
