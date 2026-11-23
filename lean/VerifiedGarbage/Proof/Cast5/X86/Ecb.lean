module

public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Cast5.Rotate
public import VerifiedGarbage.Proof.Cast5.Round
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Proof.Cast5.X86.Run
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.Sse
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.X86.SseLanes
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
public import VerifiedGarbage.Impl.Cast5.X86

/-! ### `Cast5.X86.Round`, which this module and modules that import it used -/

section

/-! ### `Cast5.X86.Scan`, which this module and modules that import it used -/

section

/-!
# CAST5 on 32-bit x86: the scan of a table

`scan sym` obtains the address `T` of `sym` in a four-byte frame below `esp`,
then visits the 256 entries of 16 bytes of the table at `T`, in order, and
leaves in each dword lane `k` of `xmm1` dword `k` of the entry whose number
is in lane `k` of `xmm0` (`scan_ok`). Vector values are kept as their four
dword lanes (`L`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.Lanes VG.X86.RegUpd VG.Impl.Cast5.X86
open VG.Impl.Cast5 (table)
open VG.Proof.Cast5 (ent Held tableEnt ent_table flatMap_range_succ)

/-! ## One entry -/

/-- Lane `k` of the result once entries `0 … j - 1` are visited. -/
def acc (tab : Nat → Nat → BitVec 32) (idx : Nat → BitVec 32) (j k : Nat) : BitVec 32 :=
  if (idx k).toNat < j then tab (idx k).toNat k else 0

/-- Every lane `n`. -/
def splat (n : Nat) : Nat → BitVec 32 := fun _ => BitVec.ofNat 32 n

theorem acc_succ (tab : Nat → Nat → BitVec 32) (idx : Nat → BitVec 32) {j : Nat} (hj : j < 256) (k : Nat) :
    (acc tab idx j k ||| (tab j k &&& if idx k = BitVec.ofNat 32 j then 0xFFFFFFFF else 0)) =
      acc tab idx (j + 1) k := by
  unfold acc
  by_cases h : idx k = BitVec.ofNat 32 j
  · have hn : (idx k).toNat = j := by rw [h, BitVec.toNat_ofNat]; omega_arith
    rw [ite_eq_left h, ite_eq_right (by omega_arith), ite_eq_left (by omega_arith), hn]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
    rw [show (0xFFFFFFFF : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.getLsbD_allOnes]
    simp [hi]
  · have hn : (idx k).toNat ≠ j := fun h' => h (BitVec.eq_of_toNat_eq (by
      rw [h', BitVec.toNat_ofNat]; omega_arith))
    rw [ite_eq_right h, show ∀ y : BitVec 32, y &&& 0 = 0 from fun y => BitVec.eq_of_getLsbD_eq (by simp),
      show ∀ y : BitVec 32, y ||| 0 = y from fun y => BitVec.eq_of_getLsbD_eq (by simp)]
    by_cases h2 : (idx k).toNat < j
    · rw [ite_eq_left h2, ite_eq_left (by omega_arith)]
    · rw [ite_eq_right h2, ite_eq_right (by omega_arith)]

/-- What the loop of a scan keeps of a state. -/
structure LoopKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r
  x0 : t.xmm .xmm0 = s.xmm .xmm0
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem LoopKeep.trans {s t u : State} (h : LoopKeep s t) (h' : LoopKeep t u) : LoopKeep s u :=
  ⟨fun r a b c => (h'.gpr r a b c).trans (h.gpr r a b c), h'.x0.trans h.x0, h'.mem.trans h.mem,
   h'.rd.trans h.rd, h'.wr.trans h.wr, h'.syms.trans h.syms⟩

/-- `LoopKeep s t` for `t` made from `s` by writes of `eax`, `ecx`, `edx`, the
flags and registers other than `xmm0`. -/
tactic_template "loop_keep" : tactic => `(tactic| (
                   refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
                   · intro r ha hc hd
                     simp only [gpr_setXmm, gpr_setReg, ha, hc, hd, gpr_setFlags, gpr_arithFlags, ite_false]
                   all_goals simp (disch := decide) only [xmm_setXmm_of_ne, xmm_setReg', xmm_setFlags',
                     xmm_arithFlags', mem_setXmm, mem_setReg, mem_setFlags, mem_arithFlags, rd_setXmm, rd_setReg, rd_setFlags,
                     rd_arithFlags, wr_setXmm, wr_setReg, wr_setFlags, wr_arithFlags, syms_setXmm', syms_setReg',
                     syms_setFlags', syms_arithFlags']))

/-- The state of the scan with entries `0 … j - 1` visited, from `s₀`. -/
structure ScanAt (s₀ : State) (tab : Nat → Nat → BitVec 32) (idx : Nat → BitVec 32) (j : Nat)
    (s : State) : Prop where
  x0 : s.xmm .xmm0 = L idx
  x1 : s.xmm .xmm1 = L (acc tab idx j)
  x2 : s.xmm .xmm2 = L (splat j)
  x3 : s.xmm .xmm3 = L (splat 1)
  x6 : s.xmm .xmm6 = L (splat 0xFFFFFFFF)
  keep : LoopKeep s₀ s

theorem entry_ok {s₀ s : State} {tab : Nat → Nat → BitVec 32} {idx : Nat → BitVec 32} {j : Nat} (e : Nat)
    (hj : j < 256) (hidx : ∀ k < 4, (idx k).toNat < 256) (h : ScanAt s₀ tab idx j s)
    (hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .ecx) (16 * e)) 16)
    (hv : ∀ k < 4, s.mem.readW (addr (s.gpr .ecx) (16 * e) + BitVec.ofNat 64 (4 * k)) 32 = tab j k) :
    WP isa (.block (scanEntry e)) s fun t => ScanAt s₀ tab idx (j + 1) t ∧ t.gpr = s.gpr := by
  obtain ⟨h0, h1, h2, h3, h6, hk⟩ := h
  unfold scanEntry
  crun [hr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [xmm_setXmm_self, xmm_setXmm_of_ne, movdqa_L]
  · exact h0
  · rw [h0, h1, h2, h6, pxor_L, paddd_L, psrld_L, pslld_L, por_L, readW128_L, pand_L, por_L]
    refine L_congr fun k hk => ?_
    rw [hv k hk, show splat j k = BitVec.ofNat 32 j from rfl,
      show splat 0xFFFFFFFF k = (0xFFFFFFFF : BitVec 32) from rfl, mask_eq (hidx k hk) hj]
    exact acc_succ tab idx hj k
  · rw [h2, h3, paddd_L]
    refine L_congr fun k _ => ?_
    simp only [splat, BitVec.ofNat_add]
  · exact h3
  · exact h6
  · exact hk.trans (by loop_keep)

theorem entries_ok {s₀ s : State} {tab : Nat → Nat → BitVec 32} {idx : Nat → BitVec 32} {q : Nat}
    (hq : q < 64) (hidx : ∀ k < 4, (idx k).toNat < 256)
    (hr : ∀ e < 4, InRegions (s.rd ++ s.wr) (addr (s.gpr .ecx) (16 * e)) 16)
    (hv : ∀ e < 4, ∀ k < 4,
      s.mem.readW (addr (s.gpr .ecx) (16 * e) + BitVec.ofNat 64 (4 * k)) 32 = tab (4 * q + e) k) :
    ∀ e ≤ 4, ScanAt s₀ tab idx (4 * q) s →
      WP isa (.block ((List.range e).flatMap scanEntry)) s
        fun t => ScanAt s₀ tab idx (4 * q + e) t ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  intro e he h
  induction e with
  | zero => exact WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | succ e ih =>
    rw [flatMap_range_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun t ⟨ht, hg, hm, hrd, hwr⟩ => ?_
    have hr' : InRegions (t.rd ++ t.wr) (addr (t.gpr .ecx) (16 * e)) 16 := by
      rw [hrd, hwr, hg]; exact hr e (by omega_arith)
    refine WP.mono (entry_ok e (by omega_arith) hidx ht hr' (fun k hk => by rw [hm, hg]; exact hv e (by omega_arith) k hk))
      fun u ⟨hu, hug⟩ => ⟨hu, hug.trans hg, ?_⟩
    refine ⟨by rw [hu.keep.mem, ← ht.keep.mem, hm], by rw [hu.keep.rd, ← ht.keep.rd, hrd],
      by rw [hu.keep.wr, ← ht.keep.wr, hwr]⟩

theorem ScanAt.keepTo {s₀ s t : State} {tab : Nat → Nat → BitVec 32} {idx : Nat → BitVec 32} {j : Nat}
    (h : ScanAt s₀ tab idx j s) (hk : LoopKeep s t) (h1 : t.xmm .xmm1 = s.xmm .xmm1)
    (h2 : t.xmm .xmm2 = s.xmm .xmm2) (h3 : t.xmm .xmm3 = s.xmm .xmm3) (h6 : t.xmm .xmm6 = s.xmm .xmm6) :
    ScanAt s₀ tab idx j t :=
  ⟨hk.x0.trans h.x0, h1.trans h.x1, h2.trans h.x2, h3.trans h.x3, h6.trans h.x6, h.keep.trans hk⟩

/-- The address of entry `e` of group `q` of the table at `T`. -/
theorem entry_addr {T : BitVec 32} (hT : T.toNat + 4096 ≤ 2 ^ 32) {q e : Nat} (hq : q < 64) (he : e < 4) :
    addr (T + BitVec.ofNat 32 (64 * q)) (16 * e) = T.setWidth 64 + BitVec.ofNat 64 (64 * q + 16 * e) := by
  rw [show addr (T + BitVec.ofNat 32 (64 * q)) (16 * e) = addr T (64 * q + 16 * e) by
    simp only [addr, BitVec.add_assoc, BitVec.ofNat_add]]
  exact addr_eq (by omega_arith)

/-- The entries of the table at `T`, as dwords. -/
def TabAt (m : Mem) (T : BitVec 32) (tab : Nat → Nat → BitVec 32) : Prop :=
  ∀ j < 256, ∀ k < 4, m.readW (T.setWidth 64 + BitVec.ofNat 64 (16 * j + 4 * k)) 32 = tab j k

theorem body_ok {s₀ s : State} {tab : Nat → Nat → BitVec 32} {idx : Nat → BitVec 32} {T : BitVec 32} {q : Nat}
    (hq : q < 64) (hidx : ∀ k < 4, (idx k).toNat < 256) (hfit : T.toNat + 4096 ≤ 2 ^ 32)
    (hT : InRegions (s₀.rd ++ s₀.wr) (T.setWidth 64) 4096) (htab : TabAt s₀.mem T tab)
    (hecx : s.gpr .ecx = T + BitVec.ofNat 32 (64 * q)) (h : ScanAt s₀ tab idx (4 * q) s) :
    WP isa (.block scanBody) s fun t => ScanAt s₀ tab idx (4 * (q + 1)) t ∧
      t.gpr .ecx = T + BitVec.ofNat 32 (64 * (q + 1)) ∧ t.gpr .edx = s.gpr .edx - 1 ∧
      t.zf = some (s.gpr .edx - 1 == 0) := by
  unfold scanBody
  rw [WP.block_append_iff]
  have hr : ∀ e < 4, InRegions (s.rd ++ s.wr) (addr (s.gpr .ecx) (16 * e)) 16 := fun e he => by
    rw [h.keep.rd, h.keep.wr, hecx, entry_addr hfit hq he]
    exact CallLay.inRegions_sub hT (by omega_arith) (by decide)
  have hv : ∀ e < 4, ∀ k < 4,
      s.mem.readW (addr (s.gpr .ecx) (16 * e) + BitVec.ofNat 64 (4 * k)) 32 = tab (4 * q + e) k :=
    fun e he k hk => by
      rw [h.keep.mem, hecx, entry_addr hfit hq he, Offset.add_add,
        show 64 * q + 16 * e + 4 * k = 16 * (4 * q + e) + 4 * k by omega_arith]
      exact htab _ (by omega_arith) k hk
  refine WP.mono (entries_ok hq hidx hr hv 4 (Nat.le_refl _) h) fun t ⟨ht, hg, _, _, _⟩ => ?_
  crun
  rw [hg, hecx, BitVec.add_assoc, ← BitVec.ofNat_add, show 64 * q + 64 = 64 * (q + 1) by omega_arith]
  exact ⟨ht.keepTo (by loop_keep) rfl rfl rfl rfl, rfl, rfl, rfl⟩

theorem acc_zero (tab : Nat → Nat → BitVec 32) (idx : Nat → BitVec 32) : L (acc tab idx 0) = 0 := by
  rw [show (0 : BitVec 128) = L fun _ => 0 by decide]
  exact L_congr fun k _ => by simp [acc]

/-- The setup of the scan: the table's address (from `eax`) in `ecx`, 64
groups to go in `edx`, nothing found yet, entry 0 next, one and all ones. -/
theorem start_ok (s : State) (tab : Nat → Nat → BitVec 32) {idx : Nat → BitVec 32} (h0 : s.xmm .xmm0 = L idx) :
    WP isa (.block scanStart) s fun t =>
      ScanAt s tab idx 0 t ∧ t.gpr .ecx = s.gpr .eax ∧ t.gpr .edx = 64 := by
  unfold scanStart
  crun
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by loop_keep⟩, rfl⟩ <;>
    simp (disch := decide) only [xmm_setXmm_self, xmm_setXmm_of_ne, xmm_setReg']
  · exact h0
  · rw [acc_zero, XBinOp.eval, BitVec.xor_self]; rfl
  · rw [show L (splat 0) = 0 by decide, XBinOp.eval, BitVec.xor_self]; rfl
  · exact bcast_L _
  · exact bcast_L _

/-- What a scan keeps of a state. -/
structure ScanKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t.gpr r = s.gpr r
  x0 : t.xmm .xmm0 = s.xmm .xmm0
  mem : Frame [below (s.gpr .esp) 4] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

/-- The table's frame, with what it keeps of the vector registers. -/
theorem symFrame_ok' (name : String) (s : State) (hsp : 4 ≤ (s.gpr .esp).toNat) :
    WP isa (.frame (.symPush .eax name) (.block []) (.pop .ecx 1)) s fun t =>
      SymAddrPost name s t ∧ t.xmm = s.xmm := by
  have hp : isa.push (.symPush .eax name) s = some (symPushed name s) := by
    simp [isa, push, symPushed, hsp, below]
  have hq : isa.pop (.pop .ecx 1) (symPushed name s) (symPushed name s) = some (symPopped name s) := by
    simp [isa, pop, symPushed, symPopped, State.setReg, arithFlags, below]
  obtain ⟨tr, t, he, hpost⟩ := symFrame_ok name s hsp
  have ht := (Exec.det he (Exec.frame hp (Exec.block (is := []) rfl) hq)).2
  refine ⟨tr, t, he, hpost, ?_⟩
  rw [ht]
  simp [symPopped, popReg, symPushed, State.setReg, arithFlags, State.setFlags]

/-- The scan: lane `k` of `xmm1` is dword `k` of the entry of the table at
`sym` whose number is lane `k` of `xmm0`. -/
theorem scan_ok (s : State) (sym : String) {tab : Nat → Nat → BitVec 32} {idx : Nat → BitVec 32}
    (h0 : s.xmm .xmm0 = L idx) (hidx : ∀ k < 4, (idx k).toNat < 256) (hsp : 4 ≤ (s.gpr .esp).toNat)
    (hfit : (s.syms sym).toNat + 4096 ≤ 2 ^ 32)
    (hT : InRegions (s.rd ++ s.wr) ((s.syms sym).setWidth 64) 4096)
    (hdis : Region.Disjoint ⟨(s.syms sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4))
    (htab : TabAt s.mem (s.syms sym) tab) :
    WP isa (scan sym) s fun t => t.xmm .xmm1 = L (fun k => tab (idx k).toNat k) ∧ ScanKeep s t := by
  unfold scan
  refine WP.seq (WP.mono (symFrame_ok' sym s hsp) fun u ⟨hu, hux⟩ => ?_)
  have hu0 : u.xmm .xmm0 = L idx := by rw [hux]; exact h0
  have hT' : InRegions (u.rd ++ u.wr) ((u.syms sym).setWidth 64) 4096 := by rw [hu.rd, hu.wr, hu.syms]; exact hT
  have htab' : TabAt u.mem (u.syms sym) tab := fun j hj k hk => by
    rw [hu.syms, ← htab j hj k hk]
    refine hu.frame.readW (r := ⟨(s.syms sym).setWidth 64, 4096⟩) ?_ ?_ (by decide)
    · exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · intro r hr; rw [List.mem_singleton] at hr; subst hr; exact hdis
  have hfit' : (u.syms sym).toNat + 4096 ≤ 2 ^ 32 := by rw [hu.syms]; exact hfit
  refine WP.seq (WP.mono (start_ok u tab hu0) fun v ⟨hv, hvc, hvd⟩ => ?_)
  rw [hu.addr] at hvc
  refine wp_countdown (cnt := .edx) (N := 64) (by decide) (by decide)
    (fun q w => ScanAt u tab idx (4 * q) w ∧ w.gpr .ecx = u.syms sym + BitVec.ofNat 32 (64 * q))
    (fun q hq w ⟨hw, hwc⟩ _ => WP.mono (body_ok hq hidx hfit' hT' htab' hwc hw) fun x ⟨hx, hxc, hxd, hz⟩ =>
      ⟨⟨hx, hxc⟩, hxd, hz⟩)
    (fun w ⟨hw, _⟩ => ⟨?_, ?_⟩) ⟨hv, by rw [hvc, hu.syms]; exact (BitVec.add_zero _).symm⟩ (by rw [hvd]; rfl)
  · rw [hw.x1]
    exact L_congr fun k hk => by rw [acc, ite_eq_left (by have := hidx k hk; omega_arith)]
  · exact ⟨fun r a b c => (hw.keep.gpr r a b c).trans (hu.gpr r (by simp [a, b])), hw.keep.x0.trans (by rw [hux]),
      by rw [hw.keep.mem]; exact hu.frame, hw.keep.rd.trans hu.rd, hw.keep.wr.trans hu.wr,
      hw.keep.syms.trans hu.syms⟩

end VG.Proof.Cast5.X86

end

end

/-!
# CAST5 on 32-bit x86: a round

`round t up` computes `I` (`mask`, `rotate`), spreads its bytes over the
lanes of `xmm0` (`spread`), scans `VG_CAST5_S1234`, stores the four values
in the working space and combines them into `f` (`combine`), then makes the
Feistel step and moves the subkeys' pointer in its slot (`feistel`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.Lanes VG.X86.RegUpd VG.Impl.Cast5.X86
open VG.Impl.Cast5 (s1234Sym)
open VG.Proof.Cast5 (tableEnt)

/-! ## The working space -/

/-- A slot of the working space at `S`, readable. -/
theorem slot_rd {s : State} {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr (S.setWidth 64) 256) {d n : Nat} (h : d + n ≤ 256) (hn : 0 < n := by decide) :
    InRegions (s.rd ++ s.wr) (addr S d) n := by
  rw [addr_off hfit d (by omega_using [h, hn])]
  obtain ⟨g, hg, hc⟩ := hw
  exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ h (by decide)

/-- A slot of the working space at `S`, writable. -/
theorem slot_wr {s : State} {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr (S.setWidth 64) 256) {d n : Nat} (h : d + n ≤ 256) (hn : 0 < n := by decide) :
    InRegions s.wr (addr S d) n := by
  rw [addr_off hfit d (by omega_using [h, hn])]
  exact CallLay.inRegions_sub hw h (by decide)

/-- Slots that do not overlap. -/
theorem slot_sep {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) {d n e k : Nat}
    (hd : d < 256) (he : e < 256) (h : d + n ≤ e ∨ e + k ≤ d) (hn : n ≤ 256) (hk : k ≤ 256) :
    Mem.Sep (addr S d) n (addr S e) k := by
  rw [addr_off hfit d (by omega_using [hd]), addr_off hfit e (by omega_using [he])]
  exact Offset.sep _ h (by omega_using [hd, hn]) (by omega_using [he, hk])

/-- The region of slot `d`, `n` bytes. -/
abbrev slotR (S : BitVec 32) (d n : Nat) : Region := ⟨S.setWidth 64 + BitVec.ofNat 64 d, n⟩

/-! ## The rotation -/

theorem rotateStep_ok (s : State) {b : Nat} (hb : b < 5) {a kb : BitVec 32}
    (hax : s.gpr .eax = a) (hcx : s.gpr .ecx = kb) :
    WP isa (.block (rotateStep b)) s fun t =>
      t.gpr .eax = Proof.Cast5.step a kb b ∧ t.gpr .ecx = (if b < 4 then kb >>> 1 else kb) ∧
      t.mem = s.mem ∧ t.xmm = s.xmm := by
  have hn : 1 ≤ 32 - 2 ^ b ∧ 32 - 2 ^ b ≤ 31 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega_using [hb]) with h | h | h | h | h <;>
      subst h <;> decide
  unfold rotateStep
  by_cases h4 : b < 4
  · rw [ite_eq_left h4]
    crun [hax, hcx, hn]
    exact ⟨rfl, by rw [ite_eq_left h4], funext fun _ => rfl⟩
  · rw [ite_eq_right h4]
    crun [hax, hcx, hn, List.append_nil]
    exact ⟨rfl, by rw [ite_eq_right h4], funext fun _ => rfl⟩

theorem rotate_ok (s : State) {a kb : BitVec 32} (hax : s.gpr .eax = a) (hcx : s.gpr .ecx = kb) :
    WP isa (.block rotate) s fun t =>
      t.gpr .eax = a.rotateLeft (kb.toNat % 32) ∧ t.mem = s.mem ∧ t.xmm = s.xmm := by
  have e : rotate = rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++ rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (rotateStep_ok s (by decide) hax hcx) fun t₁ ⟨a₁, k₁, m₁, x₁⟩ => ?_
  rw [ite_eq_left (by decide)] at k₁
  refine WP.mono (rotateStep_ok t₁ (by decide) a₁ k₁) fun t₂ ⟨a₂, k₂, m₂, x₂⟩ => ?_
  rw [ite_eq_left (by decide)] at k₂
  refine WP.mono (rotateStep_ok t₂ (by decide) a₂ k₂) fun t₃ ⟨a₃, k₃, m₃, x₃⟩ => ?_
  rw [ite_eq_left (by decide)] at k₃
  refine WP.mono (rotateStep_ok t₃ (by decide) a₃ k₃) fun t₄ ⟨a₄, k₄, m₄, x₄⟩ => ?_
  rw [ite_eq_left (by decide)] at k₄
  refine WP.mono (rotateStep_ok t₄ (by decide) a₄ k₄) fun t₅ ⟨a₅, _, m₅, x₅⟩ => ?_
  refine ⟨?_, by rw [m₅, m₄, m₃, m₂, m₁], by rw [x₅, x₄, x₃, x₂, x₁]⟩
  rw [a₅, Proof.Cast5.steps_eq]

/-! ## The indices -/

/-- Lane `k` of the indices `spread` makes of `I`: byte `3 - k` of `I`. -/
def idx (i : BitVec 32) : Nat → BitVec 32
  | 0 => i &&& 255
  | 1 => (i >>> 8) &&& 255
  | 2 => (i >>> 16) &&& 255
  | _ => i >>> 24

theorem idx_lt (i : BitVec 32) {k : Nat} (hk : k < 4) : (idx i k).toNat < 256 := by
  rcases cases4 hk with rfl | rfl | rfl | rfl
  · simp only [idx, BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · simp only [idx, BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · simp only [idx, BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  · simp only [idx, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := i.isLt; omega_using []

theorem idx_byte (i : BitVec 32) {k : Nat} (hk : k < 4) :
    BitVec.ofNat 8 (idx i k).toNat = Spec.Cast5.byte i (3 - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Spec.Cast5.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;>
    simp only [idx, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      show (255 : BitVec 32).toNat = 255 from rfl, Nat.and_two_pow_sub_one_eq_mod _ 8] <;>
    omega_using []

theorem dword_movd0 (v : BitVec 32) : dword ((0 : BitVec 96) ++ v) 0 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.mul_zero, Nat.zero_add, ite_true]

theorem lanes_eq (a b c d : BitVec 32) :
    XBinOp.eval .punpcklqdq (XBinOp.eval .punpckldq ((0 : BitVec 96) ++ a) ((0 : BitVec 96) ++ b))
      (XBinOp.eval .punpckldq ((0 : BitVec 96) ++ c) ((0 : BitVec 96) ++ d)) = ofDwords a b c d := by
  rw [punpcklqdq_eq, punpckldq_eq, punpckldq_eq]
  simp only [dword_ofDwords_0, dword_ofDwords_1, dword_movd0]

theorem spread_ok (s : State) {i : BitVec 32} (hax : s.gpr .eax = i) :
    WP isa (.block spread) s fun t => t.xmm .xmm0 = L (idx i) ∧ t.mem = s.mem := by
  unfold spread lanes
  crun [hax]
  exact lanes_eq _ _ _ _

/-! ## The round function -/

theorem mask_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {S P : BitVec 32} {km kr d : Spec.Cast5.Word}
    (hsi : s.gpr .esi = S) (hbp : s.gpr .ebp = d)
    (hp : InRegions (s.rd ++ s.wr) (addr S kpOff) 4) (hpv : s.mem.readW (addr S kpOff) 32 = P)
    (hm : InRegions (s.rd ++ s.wr) (addr P 0) 4) (hmv : s.mem.readW (addr P 0) 32 = km)
    (hr : InRegions (s.rd ++ s.wr) (addr P 64) 4) (hrv : s.mem.readW (addr P 64) 32 = kr) :
    WP isa (.block (mask t)) s fun u =>
      u.gpr .eax = Proof.Cast5.mix t km d ∧ u.gpr .ecx = kr ∧ u.mem = s.mem ∧ u.xmm = s.xmm := by
  rcases ht with rfl | rfl | rfl <;>
  · unfold mask
    crun [hsi, hbp, hp, hpv, hm, hmv, hr, hrv]
    exact ⟨rfl, funext fun _ => rfl⟩

/-- What a round needs: `(L, R)` in `ebx`, `ebp`; the working space at `S`
(`esi`), its slot `kpOff` pointing at `Kmᵢ` (and `Krᵢ` 64 bytes on); the
table; four bytes of stack below `esp`, apart from the working space and the
table. -/
structure RoundPre (s : State) (S P : BitVec 32) (km kr l r : Spec.Cast5.Word) : Prop where
  bx : s.gpr .ebx = l
  bp : s.gpr .ebp = r
  si : s.gpr .esi = S
  fitS : S.toNat + 256 ≤ 2 ^ 32
  wS : InRegions s.wr (S.setWidth 64) 256
  kp : s.mem.readW (addr S kpOff) 32 = P
  inM : InRegions (s.rd ++ s.wr) (addr P 0) 4
  valM : s.mem.readW (addr P 0) 32 = km
  inR : InRegions (s.rd ++ s.wr) (addr P 64) 4
  valR : s.mem.readW (addr P 64) 32 = kr
  sp : 4 ≤ (s.gpr .esp).toNat
  dS : Region.Disjoint ⟨S.setWidth 64, 256⟩ (below (s.gpr .esp) 4)
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  inT : InRegions (s.rd ++ s.wr) ((s.syms s1234Sym).setWidth 64) 4096
  dT : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4)
  tab : TabAt s.mem (s.syms s1234Sym) (tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1)

/-- The first block of a round: `I`, and its bytes in the lanes of `xmm0`. -/
theorem first_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {S P : BitVec 32}
    {km kr l r : Spec.Cast5.Word} (h : RoundPre s S P km kr l r) :
    WP isa (.block (mask t ++ rotate ++ spread)) s
      fun u => u.xmm .xmm0 = L (idx ((Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32))) ∧
        u.mem = s.mem := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (mask_ok s ht h.si h.bp (slot_rd h.fitS h.wS (by decide)) h.kp h.inM h.valM h.inR h.valR)
    fun u ⟨ua, uc, um, _⟩ => ?_
  refine WP.mono (rotate_ok u ua uc) fun v ⟨va, vm, _⟩ => ?_
  refine WP.mono (spread_ok v va) fun w ⟨w0, wm⟩ => ?_
  exact ⟨w0, wm.trans (vm.trans um)⟩

theorem rd_lane (m : Mem) (a : Addr) (v : BitVec 128) {j : Nat} (hj : j < 4) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (4 * j)) 32 = dword v j := readW_writeW128 m a v hj

theorem post_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool) {S P : BitVec 32}
    {v : Nat → Spec.Cast5.Word} {l r : Spec.Cast5.Word}
    (h1 : s.xmm .xmm1 = L v) (hbx : s.gpr .ebx = l) (hbp : s.gpr .ebp = r) (hsi : s.gpr .esi = S)
    (hfit : S.toNat + 256 ≤ 2 ^ 32) (hw : InRegions s.wr (S.setWidth 64) 256)
    (hp : s.mem.readW (addr S kpOff) 32 = P) :
    WP isa (.block (([.movdquStore (at_ .esi 0) .xmm1] : List Instr) ++ combine t ++ feistel up)) s
      fun u => u.gpr .ebx = r ∧
        u.gpr .ebp = l ^^^ Proof.Cast5.comb t (v 3) (v 2) (v 1) (v 0) ∧
        u.mem = (s.mem.writeW (addr S 0) (L v)).writeW (addr S kpOff) (if up then P + 4 else P - 4) ∧
        u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms ∧ u.xmm = s.xmm := by
  have e (j : Nat) (hj : j < 4) : (s.mem.writeW (addr S 0) (L v)).readW (addr S (4 * j)) 32 = v j := by
    rw [addr_off hfit (4 * j) (by omega_using [hj]), addr_off hfit 0 (by omega_using []), BitVec.add_zero, rd_lane _ _ _ hj,
      dword_L _ hj]
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  have e3 := e 3 (by decide)
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at e0 e1 e2 e3
  have eP : (s.mem.writeW (addr S 0) (L v)).readW (addr S kpOff) 32 = P := by
    rw [Mem.readW_writeW_sep (w := 32) (w' := 128) (slot_sep hfit (d := kpOff) (n := 4) (e := 0) (k := 16)
      (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)]
    exact hp
  have r0 := slot_rd hfit hw (d := 0) (n := 4) (by decide)
  have r4 := slot_rd hfit hw (d := 4) (n := 4) (by decide)
  have r8 := slot_rd hfit hw (d := 8) (n := 4) (by decide)
  have r12 := slot_rd hfit hw (d := 12) (n := 4) (by decide)
  have rP := slot_rd hfit hw (d := kpOff) (n := 4) (by decide)
  have w0 := slot_wr hfit hw (d := 0) (n := 16) (by decide)
  have wP := slot_wr hfit hw (d := kpOff) (n := 4) (by decide)
  simp only [kpOff] at eP rP wP ⊢
  rcases ht with rfl | rfl | rfl <;> cases up <;>
  · unfold combine feistel
    crun [hsi, hbx, hbp, h1, r0, r4, r8, r12, rP, w0, wP, e0, e1, e2, e3, eP, kpOff]
    refine ⟨?_, rfl, funext fun _ => rfl⟩
    rw [BitVec.xor_comm]; rfl

/-- `f` of a round of type `t` with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

/-- The registers a round writes. -/
def roundRegs : List Reg := [.eax, .ecx, .edx, .ebx, .ebp, .edi]

/-- The memory a round writes: the stack word, the scan's result and the
subkeys' pointer. -/
def roundMem (S sp : BitVec 32) : List Region := [below sp 4, slotR S 0 16, slotR S kpOff 4]

theorem round_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (up : Bool)
    {S P : BitVec 32} {km kr l r : Spec.Cast5.Word} (h : RoundPre s S P km kr l r) :
    WP isa (round t up) s fun u =>
      u.gpr .ebx = r ∧ u.gpr .ebp = l ^^^ fT t km kr r ∧
      u.mem.readW (addr S kpOff) 32 = (if up then P + 4 else P - 4) ∧
      Frame (roundMem S (s.gpr .esp)) s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms ∧
      Keep roundRegs s u := by
  have hw : writesOnly roundRegs (round t up) = true := by
    rcases ht with rfl | rfl | rfl <;> cases up <;> decide
  suffices main : WP isa (round t up) s fun u =>
      u.gpr .ebx = r ∧ u.gpr .ebp = l ^^^ fT t km kr r ∧
      u.mem.readW (addr S kpOff) 32 = (if up then P + 4 else P - 4) ∧
      Frame (roundMem S (s.gpr .esp)) s.mem u.mem ∧ u.syms = s.syms by
    exact WP.mono (WP.keep roundRegs main hw) fun u ⟨⟨a, b, c, d, e⟩, hku⟩ =>
      ⟨a, b, c, d, hku.rd, hku.wr, e, hku⟩
  unfold round
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32) = i := ⟨_, rfl⟩
  refine WP.seq (WP.mono_syms (WP.keep [.eax, .ecx, .edx, .edi] (first_ok s ht h) (by
    rcases ht with rfl | rfl | rfl <;> decide)) fun u ⟨⟨u0, um⟩, uk⟩ usy => ?_)
  rw [hi] at u0
  have usp : u.gpr .esp = s.gpr .esp := uk.gpr .esp (by decide)
  have usi : u.gpr .esi = S := (uk.gpr .esi (by decide)).trans h.si
  refine WP.seq (WP.mono (scan_ok u s1234Sym (tab := tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1) u0 (fun k hk => idx_lt i hk) (by rw [usp]; exact h.sp)
    (by rw [usy]; exact h.fitT) (by rw [uk.rd, uk.wr, usy]; exact h.inT) (by rw [usy, usp]; exact h.dT)
    (by rw [um, usy]; exact h.tab)) fun v ⟨v1, vk⟩ => ?_)
  have g (q : Reg) (hq : q ∉ [Reg.eax, .ecx, .edx, .edi]) (ha : q ≠ .eax) (hc : q ≠ .ecx) (hd : q ≠ .edx) :
      v.gpr q = s.gpr q := (vk.gpr q ha hc hd).trans (uk.gpr q hq)
  have vsi : v.gpr .esi = S := (g .esi (by decide) (by decide) (by decide) (by decide)).trans h.si
  have hvw : InRegions v.wr (S.setWidth 64) 256 := by rw [vk.wr, uk.wr]; exact h.wS
  have vP : v.mem.readW (addr S kpOff) 32 = P := by
    have hc : Region.Contains ⟨S.setWidth 64, 256⟩ (addr S kpOff) (32 / 8) := by
      rw [addr_off h.fitS kpOff (by decide)]
      exact Offset.contains_base _ (by decide) (by decide)
    have hd : ∀ r' ∈ [below (u.gpr .esp) 4], Region.Disjoint ⟨S.setWidth 64, 256⟩ r' := by
      intro r' hr'; rw [List.mem_singleton] at hr'; subst hr'; rw [usp]; exact h.dS
    rw [vk.mem.readW hc hd (by decide), um]
    exact h.kp
  refine WP.mono (post_ok v ht up (S := S) (l := l) (r := r) v1
    (by rw [g .ebx (by decide) (by decide) (by decide) (by decide)]; exact h.bx)
    (by rw [g .ebp (by decide) (by decide) (by decide) (by decide)]; exact h.bp) vsi h.fitS hvw vP)
    fun w ⟨wbx, wbp, wm, _, _, wsy, _⟩ => ?_
  refine ⟨wbx, ?_, ?_, ?_, wsy.trans (vk.syms.trans usy)⟩
  · rw [wbp]
    congr 1
    unfold fT
    rw [hi]
    simp only [tableEnt, idx_byte i (show 0 < 4 by decide), idx_byte i (show 1 < 4 by decide),
      idx_byte i (show 2 < 4 by decide), idx_byte i (show 3 < 4 by decide)]
  · rw [wm, Mem.readW_writeW_self32]
  · rw [wm]
    have hS0 : Region.Contains (slotR S 0 16) (addr S 0) (128 / 8) := by
      rw [addr_off h.fitS 0 (by decide)]; exact Offset.contains _ (by decide) (by decide) (by decide)
    have hSP : Region.Contains (slotR S kpOff 4) (addr S kpOff) (32 / 8) := by
      rw [addr_off h.fitS kpOff (by decide)]; exact Offset.contains _ (by decide) (by decide) (by decide)
    refine Frame.writeW (Frame.writeW ?_ (by simp [roundMem]) _ hS0) (by simp [roundMem]) _ hSP
    have vf := vk.mem
    rw [um, usp] at vf
    exact vf.mono (by intro r' hr'; rw [List.mem_singleton] at hr'; subst hr'; simp [roundMem])

end VG.Proof.Cast5.X86

end

end

/-! ### `Cast5.X86.Block`, which this module and modules that import it used -/

section

/-!
# CAST5 on 32-bit x86: a block

The rounds of a block, three at a time (`group`), and `crypt`: from the block
at the data slot of the working space to its encryption or decryption there,
under the subkeys and the number of rounds in their slots.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Cast5.X86
open VG.Impl.Cast5 (s1234Sym)
open VG.Proof.Cast5 (tableEnt encFold decFold encFold_succ decFold_succ encryptBlock_eq decryptBlock_eq f_eq
  roundI decodeBlock_blockAt blockAt_write)

/-- `fT` of the type of round `i` is the spec's `f`. -/
theorem fT_eq {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3) (km kr d : Spec.Cast5.Word) :
    fT t km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]
  unfold fT roundI
  rcases ht with rfl | rfl | rfl <;> rw [← hti] <;> rfl

/-- The S-box table of the rounds. -/
abbrev tab1234 : Nat → Nat → BitVec 32 := tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2 Spec.Cast5.S1

/-- The memory a block's rounds write. -/
def blockMem (S sp : BitVec 32) : List Region := [below sp 4, slotR S 0 16, slotR S kpOff 8]

/-- What every round of a block reads: the working space at `S` (`esi`), its
slots holding the subkeys' address `K` and the number of rounds `n`, the
subkeys `k` at `K`, the table, and the word below `esp`, apart from each
other. -/
structure Ctx (s : State) (S K : BitVec 32) (k : Spec.Cast5.Schedule) (n : Nat) : Prop where
  si : s.gpr .esi = S
  fitS : S.toNat + 256 ≤ 2 ^ 32
  wS : InRegions s.wr (S.setWidth 64) 256
  schedSlot : s.mem.readW (addr S schedOff) 32 = K
  roundsSlot : s.mem.readW (addr S roundsOff) 32 = BitVec.ofNat 32 n
  nv : n = 12 ∨ n = 16
  fitK : K.toNat + 128 ≤ 2 ^ 32
  inK : InRegions (s.rd ++ s.wr) (K.setWidth 64) 128
  key : ∀ j < 32, s.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32 = k.getD j 0
  sp : 4 ≤ (s.gpr .esp).toNat
  dS : Region.Disjoint ⟨S.setWidth 64, 256⟩ (below (s.gpr .esp) 4)
  dK : Region.Disjoint ⟨K.setWidth 64, 128⟩ (below (s.gpr .esp) 4)
  dKS : Region.Disjoint ⟨K.setWidth 64, 128⟩ ⟨S.setWidth 64, 256⟩
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  inT : InRegions (s.rd ++ s.wr) ((s.syms s1234Sym).setWidth 64) 4096
  dT : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4)
  dTS : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ⟨S.setWidth 64, 256⟩
  tab : TabAt s.mem (s.syms s1234Sym) tab1234

/-- A slot region inside the working space. -/
theorem slot_sub (S : BitVec 32) {d n : Nat} (h : d + n ≤ 256) : Region.Sub (slotR S d n) ⟨S.setWidth 64, 256⟩ :=
  Offset.sub_base _ h

/-- The regions a block writes miss the subkeys, the table and the slots
`48 … 63`. -/
theorem blockMem_disjoint {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : Ctx s S K k n) :
    ∀ r ∈ blockMem S (s.gpr .esp), r.Disjoint ⟨K.setWidth 64, 128⟩ ∧
      r.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ∧ r.Disjoint (slotR S 48 16) := by
  intro r hr
  simp only [blockMem, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨h.dK.symm, h.dT.symm, (h.dS.sub_left (slot_sub S (by decide))).symm⟩
  · exact ⟨(h.dKS.sub_right (slot_sub S (by decide))).symm, (h.dTS.sub_right (slot_sub S (by decide))).symm,
      Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · exact ⟨(h.dKS.sub_right (slot_sub S (by decide))).symm, (h.dTS.sub_right (slot_sub S (by decide))).symm,
      Offset.disjoint _ (by decide) (by decide) (by decide)⟩

/-- A slot of `48 … 63`, read through a frame missing them. -/
theorem slot_frame {m m' : Mem} {rs : List Region} {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, r.Disjoint (slotR S 48 16)) {d : Nat} (h1 : 48 ≤ d) (h2 : d + 4 ≤ 64) :
    m'.readW (addr S d) 32 = m.readW (addr S d) 32 := by
  rw [addr_off hfit d (by omega_arith)]
  exact hf.readW (r := slotR S 48 16) (Offset.contains _ h1 (by omega_arith) (by omega_arith))
    (fun r hr => (hd r hr).symm) (by decide)

/-- The context holds in a state that differs only in the registers but
`esi` and `esp`, and in memory missing the subkeys, the table and the slots
`48 … 63`. -/
theorem Ctx.transfer {s u : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : Ctx s S K k n)
    (hsi : u.gpr .esi = S) (hsp : u.gpr .esp = s.gpr .esp) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr)
    (hsy : u.syms = s.syms) {rs : List Region} (hf : Frame rs s.mem u.mem)
    (hd : ∀ r ∈ rs, r.Disjoint ⟨K.setWidth 64, 128⟩ ∧ r.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ∧
      r.Disjoint (slotR S 48 16)) :
    Ctx u S K k n := by
  refine ⟨hsi, h.fitS, by rw [hwr]; exact h.wS, ?_, ?_, h.nv, h.fitK, by rw [hrd, hwr]; exact h.inK,
    fun j hj => ?_, by rw [hsp]; exact h.sp, by rw [hsp]; exact h.dS, by rw [hsp]; exact h.dK, h.dKS,
    by rw [hsy]; exact h.fitT, by rw [hrd, hwr, hsy]; exact h.inT, by rw [hsy, hsp]; exact h.dT,
    by rw [hsy]; exact h.dTS, fun j hj q hq => ?_⟩
  · rw [slot_frame h.fitS hf (fun r hr => (hd r hr).2.2) (by decide) (by decide)]; exact h.schedSlot
  · rw [slot_frame h.fitS hf (fun r hr => (hd r hr).2.2) (by decide) (by decide)]; exact h.roundsSlot
  · rw [hf.readW (r := ⟨K.setWidth 64, 128⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun r hr => (hd r hr).1.symm) (by decide)]
    exact h.key j hj
  · rw [hsy, hf.readW (r := ⟨(s.syms s1234Sym).setWidth 64, 4096⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun r hr => (hd r hr).2.1.symm) (by decide)]
    exact h.tab j hj q hq

/-- Round `i`'s precondition, with the subkeys' slot at `Kmᵢ`. -/
theorem Ctx.roundPre {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : Ctx s S K k n) {i : Nat}
    (hi : 1 ≤ i ∧ i ≤ 16) (hkp : s.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (i - 1)))
    {l r : Spec.Cast5.Word} (hbx : s.gpr .ebx = l) (hbp : s.gpr .ebp = r) :
    RoundPre s S (K + BitVec.ofNat 32 (4 * (i - 1))) (k.getD (i - 1) 0) (k.getD (15 + i) 0) l r := by
  have hK := h.fitK
  obtain a0 : addr (K + BitVec.ofNat 32 (4 * (i - 1))) 0 = K.setWidth 64 + BitVec.ofNat 64 (4 * (i - 1)) := by
    obtain e := addr_eq (x := K) (k := 4 * (i - 1)) (by omega_arith)
    unfold addr at e ⊢
    exact (congrArg (BitVec.setWidth 64) (BitVec.add_zero _)).trans e
  obtain a64 : addr (K + BitVec.ofNat 32 (4 * (i - 1))) 64 = K.setWidth 64 + BitVec.ofNat 64 (4 * (15 + i)) := by
    obtain e := addr_eq (x := K) (k := 4 * (15 + i)) (by omega_arith)
    unfold addr at e ⊢
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 4 * (i - 1) + 64 = 4 * (15 + i) by omega_arith]; exact e
  refine ⟨hbx, hbp, h.si, h.fitS, h.wS, hkp, ?_, ?_, ?_, ?_, h.sp, h.dS, h.fitT, h.inT, h.dT, h.tab⟩
  · rw [a0]; exact CallLay.inRegions_sub h.inK (by omega_arith) (by decide)
  · rw [a0]; exact h.key _ (by omega_arith)
  · rw [a64]; exact CallLay.inRegions_sub h.inK (by omega_arith) (by decide)
  · rw [a64]; exact h.key _ (by omega_arith)

/-- The state of a block's rounds, from `s`, with the halves `lr`. -/
structure RInv (s : State) (S K : BitVec 32) (k : Spec.Cast5.Schedule) (n : Nat)
    (lr : Spec.Cast5.Word × Spec.Cast5.Word) (u : State) : Prop where
  bx : u.gpr .ebx = lr.1
  bp : u.gpr .ebp = lr.2
  ctx : Ctx u S K k n
  same : ∀ q, q ∉ roundRegs → u.gpr q = s.gpr q
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  syms : u.syms = s.syms
  frame : Frame (blockMem S (s.gpr .esp)) s.mem u.mem

theorem roundMem_sub (S sp : BitVec 32) : ∀ r ∈ roundMem S sp, r ∈ blockMem S sp ∨
    Region.Sub r (slotR S kpOff 8) := by
  intro r hr
  simp only [roundMem, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inl (by simp [blockMem])
  · exact .inl (by simp [blockMem])
  · exact .inr (Offset.sub _ (by decide) (by decide))

/-- A frame of the round's regions is one of the block's. -/
theorem roundMem_frame {S sp : BitVec 32} {m m' : Mem} (h : Frame (roundMem S sp) m m') :
    Frame (blockMem S sp) m m' :=
  h.sub fun r hr => by
    rcases roundMem_sub S sp r hr with h' | h'
    · exact ⟨r, h', fun _ x => x⟩
    · exact ⟨_, by simp [blockMem], h'⟩

theorem round_step {s u : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    (h : RInv s S K k n lr u) {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3)
    (hi : 1 ≤ i ∧ i ≤ 16) (hkp : u.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (i - 1))) (up : Bool) :
    WP isa (round t up) u fun v => RInv s S K k n (Spec.Cast5.round k i lr) v ∧
      v.mem.readW (addr S kpOff) 32 =
        (if up then K + BitVec.ofNat 32 (4 * (i - 1)) + 4 else K + BitVec.ofNat 32 (4 * (i - 1)) - 4) ∧
      v.mem.readW (addr S gcOff) 32 = u.mem.readW (addr S gcOff) 32 := by
  refine WP.mono (round_ok u ht up (h.ctx.roundPre hi hkp h.bx h.bp))
    fun v ⟨vbx, vbp, vkp, vf, vrd, vwr, vsy, vk⟩ => ?_
  have g (q : Reg) (hq : q ∉ roundRegs) : v.gpr q = u.gpr q := vk.gpr q hq
  obtain usp : u.gpr .esp = s.gpr .esp := h.same .esp (by decide)
  obtain vf' := roundMem_frame vf
  refine ⟨⟨vbx, ?_, h.ctx.transfer ((g .esi (by decide)).trans h.ctx.si) (g .esp (by decide)) vrd vwr vsy vf'
      (blockMem_disjoint h.ctx), fun q hq => (g q hq).trans (h.same q hq), vrd.trans h.rd, vwr.trans h.wr,
      vsy.trans h.syms, h.frame.trans (by rw [← usp]; exact vf')⟩, vkp, ?_⟩
  · rw [vbp, fT_eq ht hti]
    rfl
  · rw [addr_off h.ctx.fitS gcOff (by decide)]
    refine vf.readW (r := slotR S gcOff 4) (Offset.contains _ (by decide) (by decide) (by decide)) ?_ (by decide)
    intro r hr
    simp only [roundMem, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (h.ctx.dS.sub_left (slot_sub S (by decide)))
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)

/-- A slot's word, after a store to another slot. -/
theorem rd_sep {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 256) (he : e + 4 ≤ 256) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr S e) v).readW (addr S d) 32 = m.readW (addr S d) 32 :=
  Mem.readW_writeW_sep (w := 32) (w' := 32) (slot_sep hfit (by omega_arith) (by omega_arith) h (by decide) (by decide))
    (by decide)

theorem RInv.init {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : Ctx s S K k n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (hbx : s.gpr .ebx = lr.1) (hbp : s.gpr .ebp = lr.2) :
    RInv s S K k n lr s :=
  ⟨hbx, hbp, h, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-- The state of the rounds is kept by code that writes registers of a
round but `ebx` and `ebp`, and the slots `kpOff` and `gcOff`. -/
theorem RInv.mono {s u v : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : RInv s S K k n lr u)
    (hbx : v.gpr .ebx = u.gpr .ebx) (hbp : v.gpr .ebp = u.gpr .ebp) (hg : ∀ q, q ∉ roundRegs → v.gpr q = u.gpr q)
    (hrd : v.rd = u.rd) (hwr : v.wr = u.wr) (hsy : v.syms = u.syms) (hf : Frame [slotR S kpOff 8] u.mem v.mem) :
    RInv s S K k n lr v := by
  obtain hd : ∀ r ∈ [slotR S kpOff 8], r.Disjoint ⟨K.setWidth 64, 128⟩ ∧
      r.Disjoint ⟨(u.syms s1234Sym).setWidth 64, 4096⟩ ∧ r.Disjoint (slotR S 48 16) := fun r hr =>
    blockMem_disjoint h.ctx r (by rw [List.mem_singleton] at hr; subst hr; simp [blockMem])
  refine ⟨hbx.trans h.bx, hbp.trans h.bp, h.ctx.transfer ((hg .esi (by decide)).trans h.ctx.si)
    (hg .esp (by decide)) hrd hwr hsy hf hd, fun q hq => (hg q hq).trans (h.same q hq), hrd.trans h.rd,
    hwr.trans h.wr, hsy.trans h.syms, h.frame.trans (hf.mono ?_)⟩
  intro r hr; rw [List.mem_singleton] at hr; subst hr
  rw [← h.same .esp (by decide)]; simp [blockMem]

theorem kp_contains (S : BitVec 32) (hfit : S.toNat + 256 ≤ 2 ^ 32) {d : Nat} (h1 : kpOff ≤ d) (h2 : d + 4 ≤ 72) :
    Region.Contains (slotR S kpOff 8) (addr S d) (32 / 8) := by
  rw [addr_off hfit d (by omega_arith)]; exact Offset.contains _ h1 (by simp only [kpOff] at h2 ⊢; omega_arith) (by decide)

/-- The count of groups left, down by one. -/
theorem countDown_ok {s u : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : RInv s S K k n lr u) :
    WP isa (.block [.mov .edx (.mem (at_ .esi gcOff)), .alu .sub .edx (imm 1), .store (at_ .esi gcOff) .edx]) u
      fun v => RInv s S K k n lr v ∧ v.mem.readW (addr S kpOff) 32 = u.mem.readW (addr S kpOff) 32 ∧
        v.mem.readW (addr S gcOff) 32 = u.mem.readW (addr S gcOff) 32 - 1 ∧
        v.zf = some (u.mem.readW (addr S gcOff) 32 - 1 == 0) := by
  have c := h.ctx
  obtain rg := slot_rd (s := u) c.fitS c.wS (d := gcOff) (n := 4) (by decide)
  obtain wg := slot_wr (s := u) c.fitS c.wS (d := gcOff) (n := 4) (by decide)
  crun [c.si, rg, wg]
  refine ⟨h.mono (by simp only [gpr_setReg]; rfl) (by simp only [gpr_setReg]; rfl) (fun q hq => ?_) rfl rfl rfl
    (Frame.writeW (Frame.refl _ _) List.mem_cons_self _ (kp_contains S c.fitS (by decide) (by decide))),
    rd_sep c.fitS _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32 _ _ _, rfl⟩
  have : q ≠ .edx := fun e => hq (by rw [e]; decide)
  simp only [gpr_arithFlags, gpr_setReg, this, ite_false]

theorem four32 : (4 : BitVec 32) = BitVec.ofNat 32 4 := rfl

theorem add_ofNat_add32 (K : BitVec 32) (a b : Nat) :
    K + BitVec.ofNat 32 a + BitVec.ofNat 32 b = K + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sub_ofNat32 (K : BitVec 32) {a b : Nat} (h : b ≤ a) :
    K + BitVec.ofNat 32 a - BitVec.ofNat 32 b = K + BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := K.isLt
  omega_arith

/-- Rounds `3 g + 1`, `3 g + 2`, `3 g + 3` of encryption. -/
theorem groupEnc_ok {s u : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {g : Nat} (hg : 3 * g + 3 ≤ 16)
    (h : RInv s S K k n (encFold k (3 * g) lr) u)
    (hkp : u.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (12 * g)) :
    WP isa (group true) u fun v => RInv s S K k n (encFold k (3 * (g + 1)) lr) v ∧
      v.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (12 * (g + 1)) ∧
      v.mem.readW (addr S gcOff) 32 = u.mem.readW (addr S gcOff) 32 - 1 ∧
      v.zf = some (u.mem.readW (addr S gcOff) 32 - 1 == 0) := by
  unfold group
  simp only [ite_true]
  refine WP.seq (WP.mono (round_step h (t := 1) (i := 3 * g + 1) (by decide) (by omega_arith) (by omega_arith)
    (by rw [hkp]; congr 2 <;> omega_arith) true) fun v₁ ⟨h₁, a₁, b₁⟩ => ?_)
  rw [ite_eq_left rfl, four32, add_ofNat_add32] at a₁
  refine WP.seq (WP.mono (round_step h₁ (t := 2) (i := 3 * g + 2) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₁]; congr 2 <;> omega_arith) true) fun v₂ ⟨h₂, a₂, b₂⟩ => ?_)
  rw [ite_eq_left rfl, four32, add_ofNat_add32] at a₂
  refine WP.seq (WP.mono (round_step h₂ (t := 3) (i := 3 * g + 3) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₂]; congr 2 <;> omega_arith) true) fun v₃ ⟨h₃, a₃, b₃⟩ => ?_)
  rw [ite_eq_left rfl, four32, add_ofNat_add32] at a₃
  refine WP.mono (countDown_ok h₃) fun v₄ ⟨h₄, a₄, b₄, z₄⟩ => ?_
  refine ⟨?_, ?_, by rw [b₄, b₃, b₂, b₁], by rw [z₄, b₃, b₂, b₁]⟩
  · rw [show 3 * (g + 1) = 3 * g + 2 + 1 by omega_arith, encFold_succ, encFold_succ, encFold_succ]
    exact h₄
  · rw [a₄, a₃]; congr 2 <;> omega_arith

/-- Rounds `n - m`, `n - m - 1`, `n - m - 2` of decryption with `n` rounds,
after the first `m`. -/
theorem groupDec_ok {s u : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {m : Nat} (hm : m + 3 ≤ n) (hn : n ≤ 16) (h3 : (n - m) % 3 = 0)
    (h : RInv s S K k n (decFold k n m lr) u)
    (hkp : u.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (n - m - 1))) :
    WP isa (group false) u fun v => RInv s S K k n (decFold k n (m + 3) lr) v ∧
      v.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (n - m - 1)) - 12 ∧
      v.mem.readW (addr S gcOff) 32 = u.mem.readW (addr S gcOff) 32 - 1 ∧
      v.zf = some (u.mem.readW (addr S gcOff) 32 - 1 == 0) := by
  unfold group
  simp only [Bool.false_eq_true, ite_false]
  refine WP.seq (WP.mono (round_step h (t := 3) (i := n - m) (by decide) (by omega_arith) (by omega_arith)
    hkp false) fun v₁ ⟨h₁, a₁, b₁⟩ => ?_)
  rw [ite_eq_right Bool.false_ne_true, four32, sub_ofNat32 _ (by omega_arith)] at a₁
  refine WP.seq (WP.mono (round_step h₁ (t := 2) (i := n - m - 1) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₁]; congr 2 <;> omega_arith) false) fun v₂ ⟨h₂, a₂, b₂⟩ => ?_)
  rw [ite_eq_right Bool.false_ne_true, four32, sub_ofNat32 _ (by omega_arith)] at a₂
  refine WP.seq (WP.mono (round_step h₂ (t := 1) (i := n - m - 2) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₂]; congr 2 <;> omega_arith) false) fun v₃ ⟨h₃, a₃, b₃⟩ => ?_)
  rw [ite_eq_right Bool.false_ne_true] at a₃
  refine WP.mono (countDown_ok h₃) fun v₄ ⟨h₄, a₄, b₄, z₄⟩ => ?_
  refine ⟨?_, ?_, by rw [b₄, b₃, b₂, b₁], by rw [z₄, b₃, b₂, b₁]⟩
  · rw [decFold_succ, decFold_succ, decFold_succ, show n - (m + 1) = n - m - 1 by omega_arith,
      show n - (m + 2) = n - m - 2 by omega_arith]
    exact h₄
  · rw [a₄, a₃]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := K.isLt
    rw [show (4 : BitVec 32).toNat = 4 from rfl, show (12 : BitVec 32).toNat = 12 from rfl]
    omega_arith

/-- The count of groups: `rounds / 4 + 1`, and ZF set iff `rounds` is 16. -/
theorem groups_eq {n : Nat} (hn : n = 12 ∨ n = 16) :
    BitVec.ofNat 32 n >>> 2 + 1 = BitVec.ofNat 32 (n / 4 + 1) ∧
      (BitVec.ofNat 32 n - BitVec.ofNat 32 16 == 0) = decide (n = 16) := by
  rcases hn with rfl | rfl <;> decide

/-- The subkeys' slot at `Km₁`, the count of groups, and ZF set iff there are
16 rounds. -/
theorem encStart_ok {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : RInv s S K k n lr s) :
    WP isa (.block (([.mov .edx (.mem (at_ .esi schedOff)), .store (at_ .esi kpOff) .edx] : List Instr) ++
      groups)) s fun u => RInv s S K k n lr u ∧ u.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (12 * 0) ∧
        u.mem.readW (addr S gcOff) 32 = BitVec.ofNat 32 (n / 4 + 1) ∧ u.zf = some (decide (n = 16)) := by
  have c := h.ctx
  obtain e1 : (s.mem.writeW (addr S kpOff) K).readW (addr S roundsOff) 32 = BitVec.ofNat 32 n := by
    rw [rd_sep c.fitS _ _ (by decide) (by decide) (by decide)]; exact c.roundsSlot
  obtain e2 : ∀ v : BitVec 32, ((s.mem.writeW (addr S kpOff) K).writeW (addr S gcOff) v).readW (addr S roundsOff) 32 =
      BitVec.ofNat 32 n := fun v => by
    rw [rd_sep c.fitS _ _ (by decide) (by decide) (by decide)]; exact e1
  obtain rs := slot_rd (s := s) c.fitS c.wS (d := schedOff) (n := 4) (by decide)
  obtain rr := slot_rd (s := s) c.fitS c.wS (d := roundsOff) (n := 4) (by decide)
  obtain wk := slot_wr (s := s) c.fitS c.wS (d := kpOff) (n := 4) (by decide)
  obtain wg := slot_wr (s := s) c.fitS c.wS (d := gcOff) (n := 4) (by decide)
  obtain ⟨g1, g2⟩ := groups_eq c.nv
  unfold groups
  crun [c.si, rs, rr, wk, wg, c.schedSlot, e1, e2, g1, g2]
  refine ⟨h.mono (by simp only [gpr_setFlags, gpr_arithFlags, gpr_setReg]; rfl)
    (by simp only [gpr_setFlags, gpr_arithFlags, gpr_setReg]; rfl) (fun q hq => ?_) rfl rfl rfl ?_, ?_, ?_⟩
  · have a : q ≠ .edx := fun e => hq (by rw [e]; decide)
    obtain b : q ≠ .ecx := fun e => hq (by rw [e]; decide)
    simp only [gpr_setFlags, gpr_arithFlags, gpr_setReg, a, b, ite_false]
  · exact Frame.writeW (Frame.writeW (Frame.refl _ _) List.mem_cons_self _
      (kp_contains S c.fitS (by decide) (by decide))) List.mem_cons_self _ (kp_contains S c.fitS (by decide) (by decide))
  · rw [rd_sep c.fitS _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    exact (BitVec.add_zero K).symm
  · rw [Mem.readW_writeW_self32]; exact g1

/-- `cmp rounds, 16`. -/
theorem cmp16_ok {s u : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : RInv s S K k n lr u) :
    WP isa (.block [.mov .ecx (.mem (at_ .esi roundsOff)), .alu .cmp .ecx (imm 16)]) u fun v =>
      RInv s S K k n lr v ∧ v.mem = u.mem ∧ v.zf = some (decide (n = 16)) := by
  have c := h.ctx
  obtain rr := slot_rd (s := u) c.fitS c.wS (d := roundsOff) (n := 4) (by decide)
  crun [c.si, rr, c.roundsSlot, (groups_eq c.nv).2]
  refine h.mono (by simp only [gpr_arithFlags, gpr_setReg]; rfl) (by simp only [gpr_arithFlags, gpr_setReg]; rfl)
    (fun q hq => ?_) rfl rfl rfl (Frame.refl _ _)
  obtain b : q ≠ .ecx := fun e => hq (by rw [e]; decide)
  simp only [gpr_arithFlags, gpr_setReg, b, ite_false]

theorem encryptBlock_ok {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : Ctx s S K k n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (hbx : s.gpr .ebx = lr.1) (hbp : s.gpr .ebp = lr.2) :
    WP isa encryptBlock s fun v => RInv s S K k n (encFold k n lr) v := by
  obtain hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 32 ∧ 3 * (n / 4) ≤ 12 := by rcases h.nv with rfl | rfl <;> decide
  unfold encryptBlock
  refine WP.seq (WP.mono (encStart_ok (RInv.init h hbx hbp)) fun u ⟨hu, ukp, ugc, _⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdownF (fun v => v.mem.readW (addr S gcOff) 32) (N := n / 4 + 1) hG.2.1 hG.1
    (fun g v => RInv s S K k n (encFold k (3 * g) lr) v ∧ v.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (12 * g))
    (fun g hg v ⟨hv, hkp⟩ _ => WP.mono (groupEnc_ok (by omega_arith) hv hkp) fun w ⟨hw, wkp, wgc, wz⟩ =>
      ⟨⟨hw, wkp⟩, wgc, wz⟩)
    (fun _ h => h) ⟨hu, ukp⟩ ugc) fun v ⟨hv, vkp⟩ => ?_)
  refine WP.seq (WP.mono (cmp16_ok hv) fun w ⟨hw, wm, wz⟩ => ?_)
  refine WP.ite (decide (n = 16)) wz (fun h16 => ?_) (fun h16 => ?_)
  · have hn : n = 16 := of_decide_eq_true h16
    refine WP.mono (round_step hw (t := 1) (i := 16) (by decide) (by decide) (by decide)
      (by rw [wm, vkp, hn]) true) fun x ⟨hx, _, _⟩ => ?_
    rw [hn, show 16 = 15 + 1 from rfl, encFold_succ]
    rw [hn] at hx
    exact hx
  · have hn : n = 12 := by
      rcases h.nv with h' | h'
      · exact h'
      · exact absurd h' (of_decide_eq_false h16)
    refine WP.block_nil ?_
    rw [hn] at hw ⊢
    exact hw

theorem decKp_eq (K : BitVec 32) {n : Nat} (hn : n = 12 ∨ n = 16) :
    BitVec.ofNat 32 n + BitVec.ofNat 32 n + (BitVec.ofNat 32 n + BitVec.ofNat 32 n) + K - 4#32 =
      K + BitVec.ofNat 32 (4 * (n - 1)) := by
  apply BitVec.eq_of_toNat_eq
  have := K.isLt
  rcases hn with rfl | rfl <;>
  · simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_arith

/-- The subkeys' slot at `Kmₙ`, the count of groups, and ZF set iff there
are 16 rounds. -/
theorem decStart_ok {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : RInv s S K k n lr s) :
    WP isa (.block (([.mov .edx (.mem (at_ .esi roundsOff)), .alu .add .edx (.reg .edx),
      .alu .add .edx (.reg .edx), .mov .ecx (.mem (at_ .esi schedOff)), .alu .add .edx (.reg .ecx),
      .alu .sub .edx (imm 4),
      .store (at_ .esi kpOff) .edx] : List Instr) ++ groups)) s fun u =>
      RInv s S K k n lr u ∧ u.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (n - 1)) ∧
        u.mem.readW (addr S gcOff) 32 = BitVec.ofNat 32 (n / 4 + 1) ∧ u.zf = some (decide (n = 16)) := by
  have c := h.ctx
  obtain e1 : ∀ v : BitVec 32, (s.mem.writeW (addr S kpOff) v).readW (addr S roundsOff) 32 = BitVec.ofNat 32 n :=
    fun v => by rw [rd_sep c.fitS _ _ (by decide) (by decide) (by decide)]; exact c.roundsSlot
  obtain e2 : ∀ v w : BitVec 32, ((s.mem.writeW (addr S kpOff) v).writeW (addr S gcOff) w).readW (addr S roundsOff) 32 =
      BitVec.ofNat 32 n := fun v w => by
    rw [rd_sep c.fitS _ _ (by decide) (by decide) (by decide)]; exact e1 v
  obtain rs := slot_rd (s := s) c.fitS c.wS (d := schedOff) (n := 4) (by decide)
  obtain rr := slot_rd (s := s) c.fitS c.wS (d := roundsOff) (n := 4) (by decide)
  obtain wk := slot_wr (s := s) c.fitS c.wS (d := kpOff) (n := 4) (by decide)
  obtain wg := slot_wr (s := s) c.fitS c.wS (d := gcOff) (n := 4) (by decide)
  obtain ⟨g1, g2⟩ := groups_eq c.nv
  unfold groups
  crun [c.si, rs, rr, wk, wg, c.schedSlot, c.roundsSlot, e1, e2, g1, g2, decKp_eq K c.nv]
  refine ⟨h.mono (by simp only [gpr_setFlags, gpr_arithFlags, gpr_setReg]; rfl)
    (by simp only [gpr_setFlags, gpr_arithFlags, gpr_setReg]; rfl) (fun q hq => ?_) rfl rfl rfl ?_, ?_, ?_⟩
  · have a : q ≠ .edx := fun e => hq (by rw [e]; decide)
    obtain b : q ≠ .ecx := fun e => hq (by rw [e]; decide)
    simp only [gpr_setFlags, gpr_arithFlags, gpr_setReg, a, b, ite_false]
  · exact Frame.writeW (Frame.writeW (Frame.refl _ _) List.mem_cons_self _
      (kp_contains S c.fitS (by decide) (by decide))) List.mem_cons_self _ (kp_contains S c.fitS (by decide) (by decide))
  · rw [rd_sep c.fitS _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]; exact g1

theorem decFold_zero (k : Spec.Cast5.Schedule) (n : Nat) (lr : Spec.Cast5.Word × Spec.Cast5.Word) :
    decFold k n 0 lr = lr := rfl

theorem decryptBlock_ok {s : State} {S K : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : Ctx s S K k n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (hbx : s.gpr .ebx = lr.1) (hbp : s.gpr .ebp = lr.2) :
    WP isa decryptBlock s fun v => RInv s S K k n (decFold k n n lr) v := by
  obtain hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 32 ∧ n % 3 + 3 * (n / 4 + 1) = n ∧ n % 3 ≤ 1 := by
    rcases h.nv with rfl | rfl <;> decide
  unfold decryptBlock
  refine WP.seq (WP.mono (decStart_ok (RInv.init h hbx hbp)) fun u ⟨hu, ukp, ugc, uz⟩ => ?_)
  -- Round 16 first, if there are 16.
  obtain first : WP isa (.ite .e (round 1 false) (.block [])) u fun v =>
      RInv s S K k n (decFold k n (n % 3) lr) v ∧
        v.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (n - n % 3 - 1)) ∧
        v.mem.readW (addr S gcOff) 32 = BitVec.ofNat 32 (n / 4 + 1) := by
    refine WP.ite (decide (n = 16)) uz (fun h16 => ?_) (fun h16 => ?_)
    · have hn : n = 16 := of_decide_eq_true h16
      refine WP.mono (round_step hu (t := 1) (i := n) (by decide) (by rw [hn]) (by omega_arith) ukp false)
        fun x ⟨hx, xkp, xgc⟩ => ?_
      obtain hd : decFold k n (n % 3) lr = Spec.Cast5.round k n lr := by
        rw [hn, show 16 % 3 = 0 + 1 from rfl, decFold_succ, decFold_zero, Nat.sub_zero]
      refine ⟨(by rw [hd]; exact hx), ?_, xgc.trans ugc⟩
      rw [xkp, ite_eq_right Bool.false_ne_true, four32, sub_ofNat32 _ (by omega_arith)]
      congr 2; omega_arith
    · have hn : n = 12 := by
        rcases h.nv with h' | h'
        · exact h'
        · exact absurd h' (of_decide_eq_false h16)
      obtain hd : decFold k n (n % 3) lr = lr := by rw [hn, show 12 % 3 = 0 from rfl, decFold_zero]
      refine WP.block_nil ⟨(by rw [hd]; exact hu), ?_, ugc⟩
      rw [ukp, hn]
  refine WP.seq (WP.mono first fun v ⟨hv, vkp, vgc⟩ => ?_)
  -- Then the groups of three.
  refine wp_countdownF (fun w => w.mem.readW (addr S gcOff) 32) (N := n / 4 + 1) hG.2.1 hG.1
    (fun g w => RInv s S K k n (decFold k n (n % 3 + 3 * g) lr) w ∧
      (n % 3 + 3 * g < n → w.mem.readW (addr S kpOff) 32 = K + BitVec.ofNat 32 (4 * (n - (n % 3 + 3 * g) - 1))))
    (fun g hg w ⟨hw, wkp⟩ _ => WP.mono (groupDec_ok (m := n % 3 + 3 * g) (by omega_arith) (by
        rcases h.nv with rfl | rfl <;> decide) (by omega_arith) hw (wkp (by omega_arith)))
      fun x ⟨hx, xkp, xgc, xz⟩ =>
        ⟨⟨(show n % 3 + 3 * (g + 1) = n % 3 + 3 * g + 3 by omega_arith) ▸ hx, fun hlt => ?_⟩, xgc, xz⟩)
    (fun w ⟨hw, _⟩ => by rw [hG.2.2.1] at hw; exact hw)
    ⟨by rw [Nat.mul_zero, Nat.add_zero]; exact hv, fun _ => by rw [Nat.mul_zero, Nat.add_zero]; exact vkp⟩ vgc
  rw [xkp, show (12 : BitVec 32) = BitVec.ofNat 32 12 from rfl, sub_ofNat32 _ (by omega_arith)]
  congr 2
  omega_arith

/-! ## A block at the data slot -/

theorem writeW_readW (m : Mem) (a : Addr) : m.writeW a (m.readW a 32) = m := by
  funext x
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, show 32 / 8 = 4 from rfl]
  split
  · rename_i h
    rw [← Mem.readW_byte m a h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rfl

/-- The 8 bytes of the block at `D`. -/
abbrev blockR (D : BitVec 32) : Region := ⟨D.setWidth 64, 8⟩

/-- What `crypt` needs: the context, and the block at `D`, the address in
the data slot, apart from the working space, the subkeys, the table and the
word below `esp`. -/
structure BPre (s : State) (S K D : BitVec 32) (k : Spec.Cast5.Schedule) (n : Nat) : Prop where
  ctx : Ctx s S K k n
  dataSlot : s.mem.readW (addr S dataOff) 32 = D
  fitD : D.toNat + 8 ≤ 2 ^ 32
  wD : InRegions s.wr (D.setWidth 64) 8
  dDS : Region.Disjoint (blockR D) ⟨S.setWidth 64, 256⟩
  dDK : Region.Disjoint (blockR D) ⟨K.setWidth 64, 128⟩
  dDT : Region.Disjoint (blockR D) ⟨(s.syms s1234Sym).setWidth 64, 4096⟩
  dDsp : Region.Disjoint (blockR D) (below (s.gpr .esp) 4)

/-- Encryption or decryption of a block. -/
def cipher (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (b : Spec.Cast5.Block) : Spec.Cast5.Block :=
  if up then Spec.Cast5.encryptBlock k n b else Spec.Cast5.decryptBlock k n b

/-- The rounds of `cipher`. -/
def fold (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (lr : Spec.Cast5.Word × Spec.Cast5.Word) :
    Spec.Cast5.Word × Spec.Cast5.Word :=
  if up then encFold k n lr else decFold k n n lr

theorem cipher_eq (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (b : Spec.Cast5.Block) :
    cipher up k n b = Spec.Cast5.encodeBlock ((fold up k n (Spec.Cast5.decodeBlock b)).2,
      (fold up k n (Spec.Cast5.decodeBlock b)).1) := by
  cases up
  · exact decryptBlock_eq k n b
  · exact encryptBlock_eq k n b

theorem addr_D0 {D : BitVec 32} (h : D.toNat + 8 ≤ 2 ^ 32) : addr D 0 = D.setWidth 64 := by
  rw [addr_off h 0 (by decide), BitVec.add_zero]

theorem load_ok {s : State} {S K D : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s S K D k n) :
    WP isa (.block load) s fun u => Ctx u S K k n ∧
      (u.gpr .ebx, u.gpr .ebp) = Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (D.setWidth 64)) ∧
      u.mem = s.mem ∧ (∀ q, q ∉ roundRegs → u.gpr q = s.gpr q) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.syms = s.syms := by
  have c := h.ctx
  obtain rd := slot_rd (s := s) c.fitS c.wS (d := dataOff) (n := 4) (by decide)
  obtain r0 : InRegions (s.rd ++ s.wr) (addr D 0) 4 := by
    rw [addr_D0 h.fitD]
    obtain ⟨g, hg, hc⟩ := h.wD
    exact (CallLay.inRegions_sub (off := 0) (l := 4) ⟨g, List.mem_append_right _ hg, hc⟩ (by omega_arith) (by decide)).imp
      fun _ ⟨a, b⟩ => ⟨a, by rwa [BitVec.add_zero] at b⟩
  obtain r4 : InRegions (s.rd ++ s.wr) (addr D 4) 4 := by
    rw [addr_off h.fitD 4 (by decide)]
    obtain ⟨g, hg, hc⟩ := h.wD
    exact CallLay.inRegions_sub ⟨g, List.mem_append_right _ hg, hc⟩ (by omega_arith) (by decide)
  unfold load
  crun [c.si, rd, h.dataSlot, r0, r4]
  refine ⟨c.transfer (by simp only [gpr_setReg]; exact c.si) rfl rfl rfl rfl (Frame.refl [] _) (by simp), ?_,
    fun q hq => ?_⟩
  · rw [decodeBlock_blockAt, addr_D0 h.fitD, addr_off h.fitD 4 (by decide)]
    rfl
  · have a : q ≠ .edx := fun e => hq (by rw [e]; decide)
    obtain b : q ≠ .ebx := fun e => hq (by rw [e]; decide)
    obtain d : q ≠ .ebp := fun e => hq (by rw [e]; decide)
    simp only [a, b, d, ite_false]

/-- What `crypt` does. -/
structure BPost (s : State) (S D : BitVec 32) (out : Spec.Cast5.Block) (v : State) : Prop where
  blk : Spec.Cast5.blockAt v.mem (D.setWidth 64) = out
  frame : Frame (blockR D :: blockMem S (s.gpr .esp)) s.mem v.mem
  same : ∀ q, q ∉ roundRegs → v.gpr q = s.gpr q
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  syms : v.syms = s.syms

/-- A slot of `48 … 63` through the writes of a block. -/
theorem slot_block {m : Mem} {S D : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) (hD : D.toNat + 8 ≤ 2 ^ 32)
    (hd : Region.Disjoint (blockR D) ⟨S.setWidth 64, 256⟩) (x y : BitVec 32) {e : Nat} (h1 : 48 ≤ e)
    (h2 : e + 4 ≤ 64) :
    ((m.writeW (addr D 0) x).writeW (addr D 4) y).readW (addr S e) 32 = m.readW (addr S e) 32 := by
  have hs (o : Nat) (ho : o + 4 ≤ 8) : Mem.Sep (addr S e) 4 (addr D o) 4 := by
    refine Region.Disjoint.sep hd.symm ?_ ?_
    · rw [addr_off hfit e (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · rw [addr_off hD o (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  rw [Mem.readW_writeW_sep (w' := 32) (hs 4 (by decide)) (by decide),
    Mem.readW_writeW_sep (w' := 32) (hs 0 (by decide)) (by decide)]

theorem store_ok {s u : State} {S K D : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat}
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} (h : BPre s S K D k n) (hu : RInv s S K k n lr u) :
    WP isa (.block store) u (BPost s S D (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have c := hu.ctx
  obtain usp : u.gpr .esp = s.gpr .esp := hu.same .esp (by decide)
  obtain uD : u.mem.readW (addr S dataOff) 32 = D := by
    rw [slot_frame c.fitS hu.frame (fun r hr => (blockMem_disjoint h.ctx r hr).2.2) (by decide) (by decide)]
    exact h.dataSlot
  obtain ⟨N, hN⟩ : ∃ N, u.mem.readW (addr S nOff) 32 = N := ⟨_, rfl⟩
  obtain w0 : InRegions u.wr (addr D 0) 4 := by
    rw [addr_D0 h.fitD, hu.wr]
    obtain ⟨g, hg, hc⟩ := h.wD
    exact ⟨g, hg, by unfold Region.Contains at hc ⊢; omega_arith⟩
  obtain w4 : InRegions u.wr (addr D 4) 4 := by
    rw [addr_off h.fitD 4 (by decide), hu.wr]
    exact CallLay.inRegions_sub h.wD (by omega_arith) (by decide)
  obtain rdD := slot_rd (s := u) c.fitS c.wS (d := dataOff) (n := 4) (by decide)
  obtain rsS := slot_rd (s := u) c.fitS c.wS (d := schedOff) (n := 4) (by decide)
  obtain rrR := slot_rd (s := u) c.fitS c.wS (d := roundsOff) (n := 4) (by decide)
  obtain rnN := slot_rd (s := u) c.fitS c.wS (d := nOff) (n := 4) (by decide)
  obtain wdD := slot_wr (s := u) c.fitS c.wS (d := dataOff) (n := 4) (by decide)
  obtain wsS := slot_wr (s := u) c.fitS c.wS (d := schedOff) (n := 4) (by decide)
  obtain wrR := slot_wr (s := u) c.fitS c.wS (d := roundsOff) (n := 4) (by decide)
  obtain wnN := slot_wr (s := u) c.fitS c.wS (d := nOff) (n := 4) (by decide)
  have hbx := hu.bx
  have hbp := hu.bp
  -- The block written, then the public slots written back with what they hold.
  obtain ⟨m', hm'⟩ : ∃ m', (u.mem.writeW (addr D 0) (byteRev32 lr.2)).writeW (addr D 4) (byteRev32 lr.1) = m' :=
    ⟨_, rfl⟩
  have sb (e : Nat) (h1 : 48 ≤ e) (h2 : e + 4 ≤ 64) : m'.readW (addr S e) 32 = u.mem.readW (addr S e) 32 := by
    rw [← hm']; exact slot_block c.fitS h.fitD (h.dDS) _ _ h1 h2
  obtain e : (((m'.writeW (addr S dataOff) D).writeW (addr S schedOff) K).writeW (addr S roundsOff)
      (BitVec.ofNat 32 n)).writeW (addr S nOff) N = m' := by
    rw [← uD, ← sb dataOff (by decide) (by decide), writeW_readW, ← c.schedSlot, ← sb schedOff (by decide) (by decide),
      writeW_readW, ← c.roundsSlot, ← sb roundsOff (by decide) (by decide), writeW_readW, ← hN,
      ← sb nOff (by decide) (by decide), writeW_readW]
  unfold store
  crun [c.si, rdD, rsS, rrR, rnN, uD, c.schedSlot, c.roundsSlot, hN, w0, w4, wdD, wsS, wrR, wnN, hbx, hbp,
    bswap_eq, hm', e]
  refine ⟨?_, ?_, fun q hq => ?_, hu.rd, hu.wr, hu.syms⟩
  · rw [← hm', addr_D0 h.fitD, addr_off h.fitD 4 (by decide), blockAt_write]
  · rw [← hm']
    obtain c0 : (blockR D).Contains (addr D 0) (32 / 8) := by
      rw [addr_D0 h.fitD]; simp [Region.Contains]
    obtain c4 : (blockR D).Contains (addr D 4) (32 / 8) := by
      rw [addr_off h.fitD 4 (by decide)]; exact Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by decide) (by decide)
    obtain f1 := (hu.frame.mono (rs' := blockR D :: blockMem S (s.gpr .esp))
      (fun r hr => List.mem_cons_of_mem _ hr)).writeW List.mem_cons_self (byteRev32 lr.2) c0
    exact f1.writeW List.mem_cons_self (byteRev32 lr.1) c4
  · have a : q ≠ .edx := fun e => hq (by rw [e]; decide)
    obtain b : q ≠ .eax := fun e => hq (by rw [e]; decide)
    obtain d : q ≠ .ecx := fun e => hq (by rw [e]; decide)
    obtain f : q ≠ .edi := fun e => hq (by rw [e]; decide)
    obtain g : q ≠ .ebx := fun e => hq (by rw [e]; decide)
    obtain i : q ≠ .ebp := fun e => hq (by rw [e]; decide)
    simp only [gpr_setReg, a, b, d, f, g, i, ite_false]
    exact hu.same q hq

theorem crypt_ok {s : State} {S K D : BitVec 32} {k : Spec.Cast5.Schedule} {n : Nat} (h : BPre s S K D k n)
    (up : Bool) :
    WP isa (crypt up) s (BPost s S D (cipher up k n (Spec.Cast5.blockAt s.mem (D.setWidth 64)))) := by
  unfold crypt
  refine WP.seq (WP.mono (load_ok h) fun u ⟨hu, hlr, um, ug, urd, uwr, usy⟩ => ?_)
  obtain usp : u.gpr .esp = s.gpr .esp := ug .esp (by decide)
  obtain hb : BPre u S K D k n := ⟨hu, by rw [um]; exact h.dataSlot, h.fitD, by rw [uwr]; exact h.wD, h.dDS, h.dDK,
    by rw [usy]; exact h.dDT, by rw [usp]; exact h.dDsp⟩
  obtain ⟨lr, hlr'⟩ : ∃ lr, Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (D.setWidth 64)) = lr := ⟨_, rfl⟩
  rw [hlr'] at hlr
  obtain hbx : u.gpr .ebx = lr.1 := by rw [← hlr]
  obtain hbp : u.gpr .ebp = lr.2 := by rw [← hlr]
  have post (v : State) (hv : RInv u S K k n (fold up k n lr) v) :
      WP isa (.block store) v (BPost s S D (cipher up k n (Spec.Cast5.blockAt s.mem (D.setWidth 64)))) := by
    refine WP.mono (store_ok hb hv) fun w hw => ?_
    rw [cipher_eq, hlr']
    exact ⟨hw.blk, by rw [← um, ← usp]; exact hw.frame, fun q hq => (hw.same q hq).trans (ug q hq),
      hw.rd.trans urd, hw.wr.trans uwr, hw.syms.trans usy⟩
  cases up
  · exact WP.seq (WP.mono (decryptBlock_ok hu hbx hbp) fun v hv => post v hv)
  · exact WP.seq (WP.mono (encryptBlock_ok hu hbx hbp) fun v hv => post v hv)

end VG.Proof.Cast5.X86

end

end

/-!
# CAST5 on 32-bit x86: ECB

`ecb up` takes the working space from the stack, saves the callee-saved
registers in it, keeps its arguments in their slots, runs `crypt` on each
block in turn (`ecbLoop_ok`) and restores the registers (`ecb_correct`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Cast5.X86
open VG.Impl.Cast5 (s1234Sym s1234)
open VG.Proof.Cast5 (tableEnt Held)

/-! ## Frames of the layouts -/

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨Q, 8⟩ r) : Spec.Cast5.blockAt m' Q = Spec.Cast5.blockAt m Q := by
  apply Vector.ext
  intro j hj
  rw [Proof.Cast5.blockAt_get _ _ hj, Proof.Cast5.blockAt_get _ _ hj]
  exact hf.bytes (R := ⟨Q, 8⟩) hd (by show (8 : Nat) ≤ 2 ^ 64; decide) hj

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨K, 128⟩ r) : Spec.Cast5.scheduleAt m' K = Spec.Cast5.scheduleAt m K := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Cast5.scheduleAt, Vector.getElem_ofFn]
  rw [hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 3 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 2 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 1 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i < 128 by omega_arith)]

/-- The table's words, as the scans read them. -/
theorem tabAt_of_held {m : Mem} {T : BitVec 32} (h : Held m (T.setWidth 64) s1234) : TabAt m T tab1234 :=
  fun _ hj _ hk => Proof.Cast5.ent_table h hj hk

theorem s1234_length : s1234.length = 512 := Proof.Cast5.table_length _ _ _ _

theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} (h : Held m T s1234) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 4096⟩ r) : Held m' T s1234 := by
  intro i hi
  rw [s1234_length] at hi
  rw [← h i (by rw [s1234_length]; exact hi)]
  exact hf.readW (r := ⟨T, 4096⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith)) hd (by decide)

/-! ## The layout -/

/-- The regions the loop writes: the data, the scan's result, the slots of
the data, the count, the subkeys' pointer and the count of groups, and the
word below `esp`. -/
def loopMem (S D : BitVec 32) (N : Nat) (sp : BitVec 32) : List Region :=
  [⟨D.setWidth 64, 8 * N⟩, slotR S 0 16, slotR S dataOff 16, below sp 4]

/-- What the loop needs of the layout, from the state `s` on entry and the
memory `m0` after the setup: the schedule `k` at `K`, the `N` blocks at `D`,
the working space at `S`, the table and the word below `esp`, separate and
within the address space; the slots of the subkeys and the rounds. -/
structure Lay (s : State) (m0 : Mem) (S D K : BitVec 32) (k : Spec.Cast5.Schedule) (n N : Nat) : Prop where
  fitS : S.toNat + 256 ≤ 2 ^ 32
  fitD : D.toNat + 8 * N ≤ 2 ^ 32
  fitK : K.toNat + 128 ≤ 2 ^ 32
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  wS : InRegions s.wr (S.setWidth 64) 256
  wD : InRegions s.wr (D.setWidth 64) (8 * N)
  inK : InRegions (s.rd ++ s.wr) (K.setWidth 64) 128
  inT : InRegions (s.rd ++ s.wr) ((s.syms s1234Sym).setWidth 64) 4096
  sp : 4 ≤ (s.gpr .esp).toNat
  dDS : Region.Disjoint ⟨D.setWidth 64, 8 * N⟩ ⟨S.setWidth 64, 256⟩
  dKS : Region.Disjoint ⟨K.setWidth 64, 128⟩ ⟨S.setWidth 64, 256⟩
  dKD : Region.Disjoint ⟨K.setWidth 64, 128⟩ ⟨D.setWidth 64, 8 * N⟩
  dTS : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ⟨S.setWidth 64, 256⟩
  dTD : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ⟨D.setWidth 64, 8 * N⟩
  dS : Region.Disjoint ⟨S.setWidth 64, 256⟩ (below (s.gpr .esp) 4)
  dD : Region.Disjoint ⟨D.setWidth 64, 8 * N⟩ (below (s.gpr .esp) 4)
  dK : Region.Disjoint ⟨K.setWidth 64, 128⟩ (below (s.gpr .esp) 4)
  dT : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4)
  nv : n = 12 ∨ n = 16
  sk : Spec.Cast5.scheduleAt m0 (K.setWidth 64) = k
  held : Held m0 ((s.syms s1234Sym).setWidth 64) s1234
  schedSlot : m0.readW (addr S schedOff) 32 = K
  roundsSlot : m0.readW (addr S roundsOff) 32 = BitVec.ofNat 32 n

/-- The state of ECB with `j` of the `N` blocks done. -/
structure LInv (s : State) (m0 : Mem) (up : Bool) (S D : BitVec 32) (k : Spec.Cast5.Schedule) (n N j : Nat)
    (u : State) : Prop where
  si : u.gpr .esi = S
  sp : u.gpr .esp = s.gpr .esp
  fr : Frame (loopMem S D N (s.gpr .esp)) m0 u.mem
  blocks : ∀ i < N, Spec.Cast5.blockAt u.mem (D.setWidth 64 + BitVec.ofNat 64 (8 * i)) =
    if i < j then cipher up k n (Spec.Cast5.blockAt m0 (D.setWidth 64 + BitVec.ofNat 64 (8 * i)))
    else Spec.Cast5.blockAt m0 (D.setWidth 64 + BitVec.ofNat 64 (8 * i))
  dslot : u.mem.readW (addr S dataOff) 32 = D + BitVec.ofNat 32 (8 * j)
  nslot : u.mem.readW (addr S nOff) 32 = BitVec.ofNat 32 (N - j)
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  syms : u.syms = s.syms

theorem setWidth_blk {D : BitVec 32} {N j : Nat} (hd : D.toNat + 8 * N ≤ 2 ^ 32) (hj : j < N) :
    (D + BitVec.ofNat 32 (8 * j)).setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 (8 * j) :=
  addr_eq (x := D) (k := 8 * j) (by omega_arith)

theorem sub_blk (P : Addr) {N j : Nat} (hj : j < N) :
    Region.Sub ⟨P + BitVec.ofNat 64 (8 * j), 8⟩ ⟨P, 8 * N⟩ := Offset.sub_base _ (by omega_arith)

/-- The regions the loop writes miss the subkeys, the table and the slots
`32 … 55`. -/
theorem loopMem_disjoint {s : State} {m0 : Mem} {S D K : BitVec 32} {k : Spec.Cast5.Schedule} {n N : Nat}
    (hl : Lay s m0 S D K k n N) : ∀ r ∈ loopMem S D N (s.gpr .esp), r.Disjoint ⟨K.setWidth 64, 128⟩ ∧
      r.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ∧ r.Disjoint (slotR S 32 24) := by
  intro r hr
  simp only [loopMem, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨hl.dKD.symm, hl.dTD.symm, hl.dDS.sub_right (slot_sub S (by decide))⟩
  · exact ⟨(hl.dKS.sub_right (slot_sub S (by decide))).symm, (hl.dTS.sub_right (slot_sub S (by decide))).symm,
      Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · exact ⟨(hl.dKS.sub_right (slot_sub S (by decide))).symm, (hl.dTS.sub_right (slot_sub S (by decide))).symm,
      Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · exact ⟨hl.dK.symm, hl.dT.symm, (hl.dS.sub_left (slot_sub S (by decide))).symm⟩

theorem slot32_frame {m m' : Mem} {rs : List Region} {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, r.Disjoint (slotR S 32 24)) {d : Nat} (h1 : 32 ≤ d) (h2 : d + 4 ≤ 56) :
    m'.readW (addr S d) 32 = m.readW (addr S d) 32 := by
  rw [addr_off hfit d (by omega_arith)]
  exact hf.readW (r := slotR S 32 24) (Offset.contains _ h1 (by omega_arith) (by omega_arith))
    (fun r hr => (hd r hr).symm) (by decide)

/-- `crypt`'s precondition, at block `j`. -/
theorem LInv.bpre {s u : State} {m0 : Mem} {up : Bool} {S D K : BitVec 32} {k : Spec.Cast5.Schedule} {n N j : Nat}
    (hl : Lay s m0 S D K k n N) (h : LInv s m0 up S D k n N j u) (hj : j < N) :
    BPre u S K (D + BitVec.ofNat 32 (8 * j)) k n := by
  obtain hd := loopMem_disjoint hl
  obtain eD := setWidth_blk hl.fitD hj
  obtain hsub : Region.Sub (blockR (D + BitVec.ofNat 32 (8 * j))) ⟨D.setWidth 64, 8 * N⟩ := by
    rw [blockR, eD]; exact sub_blk _ hj
  refine ⟨⟨h.si, hl.fitS, by rw [h.wr]; exact hl.wS, ?_, ?_, hl.nv, hl.fitK, by rw [h.rd, h.wr]; exact hl.inK,
    fun i hi => ?_, by rw [h.sp]; exact hl.sp, by rw [h.sp]; exact hl.dS, by rw [h.sp]; exact hl.dK, hl.dKS,
    by rw [h.syms]; exact hl.fitT, by rw [h.rd, h.wr, h.syms]; exact hl.inT, by rw [h.syms, h.sp]; exact hl.dT,
    by rw [h.syms]; exact hl.dTS, ?_⟩, h.dslot, ?_, ?_, hl.dDS.sub_left hsub, (hl.dKD.symm).sub_left hsub,
    by rw [h.syms]; exact (hl.dTD.symm).sub_left hsub, by rw [h.sp]; exact hl.dD.sub_left hsub⟩
  · rw [slot32_frame hl.fitS h.fr (fun r hr => (hd r hr).2.2) (by decide) (by decide)]; exact hl.schedSlot
  · rw [slot32_frame hl.fitS h.fr (fun r hr => (hd r hr).2.2) (by decide) (by decide)]; exact hl.roundsSlot
  · rw [← Proof.Cast5.scheduleAt_getD _ _ hi, scheduleAt_frame h.fr (fun r hr => ((hd r hr).1).symm), hl.sk]
  · rw [h.syms]
    exact tabAt_of_held (held_frame hl.held h.fr fun r hr => ((hd r hr).2.1).symm)
  · have := hl.fitD
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * j) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [h.wr, eD]
    exact CallLay.inRegions_sub hl.wD (by omega_arith) (by have := hl.fitD; omega_arith)

/-! ## The loop over the blocks -/

theorem ofNat_sub_one {a : Nat} (ha : 1 ≤ a) (hb : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 1 = BitVec.ofNat 32 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

/-- `advance`: on to the next block. -/
theorem advance_ok (v : State) {S : BitVec 32} (hsi : v.gpr .esi = S) (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions v.wr (S.setWidth 64) 256) {x y : BitVec 32}
    (hx : v.mem.readW (addr S dataOff) 32 = x) (hy : v.mem.readW (addr S nOff) 32 = y) :
    WP isa (.block advance) v fun w =>
      w.mem = (v.mem.writeW (addr S dataOff) (x + BitVec.ofNat 32 8)).writeW (addr S nOff) (y - BitVec.ofNat 32 1) ∧
      w.zf = some (y - BitVec.ofNat 32 1 == 0) ∧ w.gpr .esi = S ∧ w.gpr .esp = v.gpr .esp ∧ w.rd = v.rd ∧ w.wr = v.wr ∧
      w.syms = v.syms := by
  obtain hy' : (v.mem.writeW (addr S dataOff) (x + BitVec.ofNat 32 8)).readW (addr S nOff) 32 = y := by
    rw [rd_sep hfit _ _ (by decide) (by decide) (by decide)]; exact hy
  obtain rD := slot_rd (s := v) hfit hw (d := dataOff) (n := 4) (by decide)
  obtain rN := slot_rd (s := v) hfit hw (d := nOff) (n := 4) (by decide)
  obtain wD := slot_wr (s := v) hfit hw (d := dataOff) (n := 4) (by decide)
  obtain wN := slot_wr (s := v) hfit hw (d := nOff) (n := 4) (by decide)
  unfold advance
  crun [hsi, rD, rN, wD, wN, hx, hy']

theorem dslot_contains (S : BitVec 32) (hfit : S.toNat + 256 ≤ 2 ^ 32) {d : Nat} (h1 : dataOff ≤ d)
    (h2 : d + 4 ≤ 72) : Region.Contains (slotR S dataOff 16) (addr S d) (32 / 8) := by
  rw [addr_off hfit d (by omega_arith)]; exact Offset.contains _ h1 (by simp only [dataOff] at h2 ⊢; omega_arith) (by decide)

/-- A block and another. -/
theorem blk_disj_blk (P : Addr) {N i j : Nat} (hi : i < N) (hj : j < N) (hN : 8 * N ≤ 2 ^ 32) (hij : i ≠ j) :
    Region.Disjoint ⟨P + BitVec.ofNat 64 (8 * i), 8⟩ ⟨P + BitVec.ofNat 64 (8 * j), 8⟩ :=
  Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- One block, then on to the next. -/
theorem step_ok {s u : State} {m0 : Mem} {up : Bool} {S D K : BitVec 32} {k : Spec.Cast5.Schedule} {n N j : Nat}
    (hl : Lay s m0 S D K k n N) (h : LInv s m0 up S D k n N j u) (hj : j < N) :
    WP isa (.seq (crypt up) (.block advance)) u fun w => LInv s m0 up S D k n N (j + 1) w ∧
      w.zf = some (decide (j + 1 = N)) := by
  have hdf := hl.fitD
  obtain eD := setWidth_blk hl.fitD hj
  obtain hb := h.bpre hl hj
  refine WP.seq (WP.mono (crypt_ok hb up) fun v hv => ?_)
  have vb := hv.blk
  have vf := hv.frame
  rw [blockR, eD, h.sp] at vf
  rw [eD] at vb
  obtain vsi : v.gpr .esi = S := (hv.same .esi (by decide)).trans h.si
  obtain vsp : v.gpr .esp = s.gpr .esp := (hv.same .esp (by decide)).trans h.sp
  -- The regions `crypt` wrote, against the slots of the data and the count.
  have dSl (o : Nat) (h1 : dataOff ≤ o) (h2 : o + 4 ≤ dataOff + 8) :
      ∀ r ∈ (⟨D.setWidth 64 + BitVec.ofNat 64 (8 * j), 8⟩ : Region) :: blockMem S (s.gpr .esp),
        Region.Disjoint (slotR S o 4) r := by
    intro r hr
    simp only [blockMem, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [dataOff] at h1 h2
    rcases hr with rfl | rfl | rfl | rfl
    · exact ((hl.dDS.sub_left (sub_blk _ hj)).symm.sub_left (slot_sub S (by omega_arith)))
    · exact hl.dS.sub_left (slot_sub S (by omega_arith))
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by decide)
    · exact Offset.disjoint _ (by simp only [kpOff]; omega_arith) (by omega_arith) (by decide)
  have vslot (o : Nat) (h1 : dataOff ≤ o) (h2 : o + 4 ≤ dataOff + 8) :
      v.mem.readW (addr S o) 32 = u.mem.readW (addr S o) 32 := by
    rw [addr_off hl.fitS o (by simp only [dataOff] at h2; omega_arith)]
    exact vf.readW (r := slotR S o 4)
      (Offset.contains _ (Nat.le_refl _) (Nat.le_refl _) (by simp only [dataOff] at h2; omega_arith)) (dSl o h1 h2)
      (by decide)
  obtain hw : InRegions v.wr (S.setWidth 64) 256 := by rw [hv.wr, h.wr]; exact hl.wS
  refine WP.mono (advance_ok v vsi hl.fitS hw (x := D + BitVec.ofNat 32 (8 * j)) (y := BitVec.ofNat 32 (N - j))
    (by rw [vslot dataOff (by decide) (by decide)]; exact h.dslot)
    (by rw [vslot nOff (by decide) (by decide)]; exact h.nslot)) fun w ⟨wm, wz, wsi, wsp, wrd, wwr, wsy⟩ => ?_
  -- The writes of `advance`.
  obtain fw : Frame [slotR S dataOff 16] v.mem w.mem := by
    rw [wm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (dslot_contains S hl.fitS (by decide) (by decide))).writeW
      List.mem_cons_self _ (dslot_contains S hl.fitS (by decide) (by decide))
  have dW (R : Region) (hR : Region.Disjoint R ⟨S.setWidth 64, 256⟩) : ∀ r ∈ [slotR S dataOff 16],
      Region.Disjoint R r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hR.sub_right (slot_sub S (by decide))
  refine ⟨⟨wsi, wsp.trans vsp, ?_, fun i hi => ?_, ?_, ?_, wrd.trans (hv.rd.trans h.rd),
    wwr.trans (hv.wr.trans h.wr), wsy.trans (hv.syms.trans h.syms)⟩, ?_⟩
  · refine h.fr.trans ((vf.sub fun r hr => ?_).trans (fw.mono (by simp [loopMem])))
    simp only [blockMem, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨D.setWidth 64, 8 * N⟩, by simp [loopMem], sub_blk _ hj⟩
    · exact ⟨below (s.gpr .esp) 4, by simp [loopMem], fun _ x => x⟩
    · exact ⟨slotR S 0 16, by simp [loopMem], fun _ x => x⟩
    · exact ⟨slotR S dataOff 16, by simp [loopMem], Offset.sub _ (by decide) (by decide)⟩
  · have hdi : Region.Disjoint ⟨D.setWidth 64 + BitVec.ofNat 64 (8 * i), 8⟩ ⟨S.setWidth 64, 256⟩ :=
      hl.dDS.sub_left (sub_blk _ hi)
    rw [blockAt_frame fw (dW _ hdi)]
    by_cases hij : i = j
    · subst hij
      rw [vb, ite_eq_left (by omega_arith), h.blocks i hi, ite_eq_right (by omega_arith)]
    · rw [blockAt_frame vf ?_, h.blocks i hi]
      · by_cases hlt : i < j
        · rw [ite_eq_left hlt, ite_eq_left (by omega_arith)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega_arith)]
      · intro r hr
        simp only [blockMem, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact blk_disj_blk _ hi hj (by omega_arith) hij
        · exact hl.dD.sub_left (sub_blk _ hi)
        · exact hdi.sub_right (slot_sub S (by decide))
        · exact hdi.sub_right (slot_sub S (by decide))
  · rw [wm, rd_sep hl.fitS _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, BitVec.add_assoc,
      Nat.mul_add, BitVec.ofNat_add (8 * j)]
  · rw [wm, Mem.readW_writeW_self32, ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  · rw [wz, ofNat_sub_one (by omega_arith) (by omega_arith)]
    by_cases he : j + 1 = N
    · rw [decide_eq_true he, show N - j - 1 = 0 by omega_arith]; rfl
    · rw [decide_eq_false he]
      have : BitVec.ofNat 32 (N - j - 1) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega_arith
      simpa using this

/-- The loop over the blocks, from `j = 0`: afterwards every block is done. -/
theorem ecbLoop_ok {s u : State} {m0 : Mem} {up : Bool} {S D K : BitVec 32} {k : Spec.Cast5.Schedule} {n N : Nat}
    (hl : Lay s m0 S D K k n N) (hN : 0 < N) (h : LInv s m0 up S D k n N 0 u) :
    WP isa (.loop (.seq (crypt up) (.block advance)) .ne) u (LInv s m0 up S D k n N N) := by
  refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = N - j ∧ j < N ∧ LInv s m0 up S D k n N j v)
    ?_ N u ⟨0, rfl, hN, h⟩
  rintro m v ⟨j, rfl, hj, hv⟩
  refine WP.mono (step_ok hl hv hj) fun w ⟨hw, wz⟩ => ?_
  obtain hev : isa.eval .ne w = some (!decide (j + 1 = N)) := by
    simp only [eval, wz, Option.map_some]
  by_cases he : j + 1 = N
  · exact .inl ⟨by rw [hev, decide_eq_true he]; rfl, he ▸ hw⟩
  · exact .inr ⟨by rw [hev, decide_eq_false he]; rfl, N - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hw⟩

/-! ## The whole function -/

/-- What the ECB functions need, as their proof states it: the arguments
(`schedule`, `rounds`, `data`, `n`, `scratch`) readable on the stack, the
schedule, the blocks, the working space and the table separate from each
other, from the word below `esp` and (those written) from the arguments and
the return address. -/
structure EPre (s : State) : Prop where
  rdEq : s.rd = [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 20⟩, ⟨(s.syms s1234Sym).setWidth 64, 4096⟩]
  wrEq : s.wr = [⟨(arg s 2).setWidth 64, (arg s 3).toNat * 8⟩, ⟨(arg s 4).setWidth 64, 256⟩]
  sp : 4 ≤ (s.gpr .esp).toNat
  spfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  inA : InRegions (s.rd ++ s.wr) (argAddr s 0) 20
  fitS : (arg s 4).toNat + 256 ≤ 2 ^ 32
  fitD : (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32
  fitK : (arg s 0).toNat + 128 ≤ 2 ^ 32
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  wS : InRegions s.wr ((arg s 4).setWidth 64) 256
  wD : InRegions s.wr ((arg s 2).setWidth 64) (8 * (arg s 3).toNat)
  inK : InRegions (s.rd ++ s.wr) ((arg s 0).setWidth 64) 128
  inT : InRegions (s.rd ++ s.wr) ((s.syms s1234Sym).setWidth 64) 4096
  held : Held s.mem ((s.syms s1234Sym).setWidth 64) s1234
  dDS : Region.Disjoint ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩ ⟨(arg s 4).setWidth 64, 256⟩
  dKS : Region.Disjoint ⟨(arg s 0).setWidth 64, 128⟩ ⟨(arg s 4).setWidth 64, 256⟩
  dKD : Region.Disjoint ⟨(arg s 0).setWidth 64, 128⟩ ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
  dTS : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ⟨(arg s 4).setWidth 64, 256⟩
  dTD : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
  dS : Region.Disjoint ⟨(arg s 4).setWidth 64, 256⟩ (below (s.gpr .esp) 4)
  dD : Region.Disjoint ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩ (below (s.gpr .esp) 4)
  dK : Region.Disjoint ⟨(arg s 0).setWidth 64, 128⟩ (below (s.gpr .esp) 4)
  dT : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4)
  dAS : Region.Disjoint ⟨argAddr s 0, 20⟩ ⟨(arg s 4).setWidth 64, 256⟩
  dAD : Region.Disjoint ⟨argAddr s 0, 20⟩ ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
  dRS : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 4).setWidth 64, 256⟩
  dRD : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
  nv : (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 16

/-- The ECB functions' contract on x86, as their proof states it. -/
def ecbX (up : Bool) : Contract isa where
  pre s := EPre s
  post s s' :=
    Spec.Cast5.blocksAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64)) (arg s 1).toNat
        (if up then .encrypt else .decrypt) (Spec.Cast5.blocksAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 5, arg s₁ i = arg s₂ i) ∧ s₁.syms s1234Sym = s₂.syms s1234Sym

theorem cipher_map (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (bs : List Spec.Cast5.Block) :
    bs.map (cipher up k n) = Spec.Cast5.ecb k n (if up then .encrypt else .decrypt) bs := by
  cases up <;> rfl

/-- Argument `i`, as the code reads it. -/
theorem argAddr_eq (s : State) {i : Nat} (h : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) (hi : i < 5) :
    addr (s.gpr .esp) (4 + 4 * i) = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  addr_eq (by omega_arith)

theorem arg_in {s : State} (h : EPre s) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := by
  obtain e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := argAddr_eq s (i := 0) h.spfit (by decide)
  have hA := h.inA
  rw [e0] at hA
  rw [argAddr_eq s h.spfit hi, show 4 + 4 * i = 4 + 4 * i from rfl, ← Offset.add_add]
  exact CallLay.inRegions_sub hA (by omega_arith) (by decide)

/-- The saved registers. -/
def savedL : List (Reg × Nat) := [(.ebx, savedOff), (.edi, savedOff + 8), (.ebp, savedOff + 12)]

theorem saved_eq : saved = savedL ++ [(.esi, savedOff + 4)] := rfl
theorem restore_eq : restore = Spill.restoreCode .esi saved := rfl
theorem save_eq : save = Spill.saveCode .eax saved := rfl
theorem saved_fits : Spill.Fits 256 saved := by decide

theorem saved_contains {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) :
    ∀ p ∈ saved, Region.Contains (slotR S 32 16) (addr S p.2) 4 := by
  intro p hp
  simp only [saved, savedOff, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
  · rw [addr_off hfit _ (by decide)]; exact Offset.contains _ (by decide) (by decide) (by decide)

theorem saved_in {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) :
    ∀ p ∈ saved, Region.Contains ⟨S.setWidth 64, 256⟩ (addr S p.2) 4 := by
  intro p hp
  simp only [saved, savedOff, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
  · rw [addr_off hfit _ (by decide)]; exact Offset.contains_base _ (by decide) (by decide)

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The slots of the arguments, after the setup. -/
def argMem (m : Mem) (S K R D N : BitVec 32) : Mem :=
  (((m.writeW (addr S schedOff) K).writeW (addr S roundsOff) R).writeW (addr S dataOff) D).writeW (addr S nOff) N

theorem argMem_frame (m : Mem) {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) (K R D N : BitVec 32) :
    Frame [slotR S schedOff 16] m (argMem m S K R D N) := by
  have c (d : Nat) (h1 : schedOff ≤ d) (h2 : d + 4 ≤ 64) : Region.Contains (slotR S schedOff 16) (addr S d) (32 / 8) := by
    rw [addr_off hfit d (by omega_arith)]; exact Offset.contains _ h1 (by simp only [schedOff] at h2 ⊢; omega_arith) (by decide)
  exact (((Frame.refl _ _).writeW List.mem_cons_self _ (c schedOff (by decide) (by decide))).writeW
    List.mem_cons_self _ (c roundsOff (by decide) (by decide))).writeW List.mem_cons_self _
    (c dataOff (by decide) (by decide)) |>.writeW List.mem_cons_self _ (c nOff (by decide) (by decide))

theorem ecb_correct (up : Bool) (s : State) (h : EPre s) :
    WP isa (ecb up) s fun s' => abiPreserved s s' ∧ (ecbX up).post s s' := by
  obtain ⟨S, hS⟩ : ∃ S, arg s 4 = S := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, arg s 0 = K := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, arg s 1 = R := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, arg s 2 = D := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, arg s 3 = N := ⟨_, rfl⟩
  obtain fitS : S.toNat + 256 ≤ 2 ^ 32 := hS ▸ h.fitS
  obtain wS : InRegions s.wr (S.setWidth 64) 256 := hS ▸ h.wS
  obtain a4 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 20) 4 := arg_in h (i := 4) (by decide)
  obtain a0 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 := arg_in h (i := 0) (by decide)
  obtain a1 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := arg_in h (i := 1) (by decide)
  obtain a2 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4 := arg_in h (i := 2) (by decide)
  obtain a3 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4 := arg_in h (i := 3) (by decide)
  have v4 : s.mem.readW (addr (s.gpr .esp) 20) 32 = S := hS
  -- The saved registers' memory.
  let g := (s.setReg .eax S).gpr
  let SM := Spill.saveMem s.mem (addr S) g saved
  have argSM (i : Nat) (hi : i < 4) : SM.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i := by
    refine Spill.saveMem_readW_of_sep _ _ (by decide) saved s.mem fun p hp => ?_
    refine Region.Disjoint.sep h.dAS ?_ ?_
    · have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
        argAddr_eq s (i := 0) h.spfit (by decide)
      rw [argAddr_eq s h.spfit (by omega_arith), e0, ← Offset.add_add]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · rw [hS]; exact saved_in fitS p hp
  obtain sK : SM.readW (addr (s.gpr .esp) 4) 32 = K := (argSM 0 (by decide)).trans hK
  obtain sR : SM.readW (addr (s.gpr .esp) 8) 32 = R := (argSM 1 (by decide)).trans hR
  obtain sD : SM.readW (addr (s.gpr .esp) 12) 32 = D := (argSM 2 (by decide)).trans hD
  obtain sN : SM.readW (addr (s.gpr .esp) 16) 32 = N := (argSM 3 (by decide)).trans hN
  obtain wK := slot_wr (s := s) fitS wS (d := schedOff) (n := 4) (by decide)
  obtain wR := slot_wr (s := s) fitS wS (d := roundsOff) (n := 4) (by decide)
  obtain wD := slot_wr (s := s) fitS wS (d := dataOff) (n := 4) (by decide)
  obtain wN := slot_wr (s := s) fitS wS (d := nOff) (n := 4) (by decide)
  unfold ecb
  rw [List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  obtain h1 : WP isa (.block [.mov .eax (.mem (at_ .esp 20))]) s fun s₁ => s₁ = s.setReg .eax S := by
    crun [a4, v4]
  refine WP.mono h1 fun s₁ e₁ => ?_
  subst e₁
  rw [save_eq]
  refine Spill.save_ok saved (fun p hp => ?_) fun s₂ u₂ => ?_
  · rw [wr_setReg, gpr_setReg_self]
    exact slot_wr fitS wS (d := p.2) (n := 4) (by have := saved_fits.1 p hp; omega_arith)
  have g₂ : s₂.gpr = g := u₂.gpr
  obtain m₂ : s₂.mem = SM := by rw [u₂.mem]; rfl
  have rd₂ : s₂.rd = s.rd := u₂.rd
  have wr₂ : s₂.wr = s.wr := u₂.wr
  have sy₂ : s₂.syms = s.syms := u₂.syms
  obtain hge : g .eax = S := gpr_setReg_self _ _ _
  obtain hgsp : g .esp = s.gpr .esp := gpr_setReg_of_ne _ _ (by decide)
  obtain hsetup : WP isa (.block setup) s₂ fun s₃ => s₃.mem = argMem SM S K R D N ∧ s₃.gpr .esi = S ∧
      s₃.gpr .esp = s.gpr .esp ∧ s₃.zf = some (N - BitVec.ofNat 32 0 == 0) ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      s₃.syms = s.syms := by
    unfold setup
    crun [g₂, m₂, rd₂, wr₂, sy₂, hge, hgsp, a0, a1, a2, a3, sK, sR, sD, sN, wK, wR, wD, wN]
    rfl
  refine WP.mono hsetup fun s₃ ⟨m₃, si₃, sp₃, z₃, rd₃, wr₃, sy₃⟩ => ?_
  -- The memory after the setup, and the layout.
  let m0 := argMem SM S K R D N
  obtain F : Frame [⟨S.setWidth 64, 256⟩] s.mem m0 :=
    (Spill.saveMem_frame (R := ⟨S.setWidth 64, 256⟩) List.mem_cons_self (addr S) g saved s.mem (saved_in fitS)).trans
      ((argMem_frame SM fitS K R D N).sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, slot_sub S (by decide)⟩)
  have dF (X : Region) (hX : X.Disjoint ⟨S.setWidth 64, 256⟩) : ∀ r ∈ [(⟨S.setWidth 64, 256⟩ : Region)], X.Disjoint r :=
    fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hX
  obtain hl : Lay s m0 S D K (Spec.Cast5.scheduleAt s.mem (K.setWidth 64)) R.toNat N.toNat := by
    subst hS hK hR hD hN
    refine ⟨h.fitS, h.fitD, h.fitK, h.fitT, h.wS, h.wD, h.inK, h.inT, h.sp, h.dDS, h.dKS, h.dKD, h.dTS, h.dTD,
      h.dS, h.dD, h.dK, h.dT, h.nv, scheduleAt_frame F (dF _ h.dKS), held_frame h.held F (dF _ h.dTS), ?_, ?_⟩
    · simp only [m0, argMem]
      rw [rd_sep h.fitS _ _ (by decide) (by decide) (by decide), rd_sep h.fitS _ _ (by decide) (by decide) (by decide),
        rd_sep h.fitS _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    · simp only [m0, argMem]
      rw [rd_sep h.fitS _ _ (by decide) (by decide) (by decide), rd_sep h.fitS _ _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32, ofNat_toNat32]
  obtain h0 : LInv s m0 up S D (Spec.Cast5.scheduleAt s.mem (K.setWidth 64)) R.toNat N.toNat 0 s₃ := by
    refine ⟨si₃, sp₃, by rw [m₃]; exact Frame.refl _ _, fun i hi => by rw [m₃, ite_eq_right (by omega_arith)], ?_, ?_, rd₃,
      wr₃, sy₃⟩
    · rw [m₃]
      simp only [argMem]
      rw [rd_sep fitS _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
      exact (BitVec.add_zero D).symm
    · rw [m₃]
      simp only [argMem]
      rw [Mem.readW_writeW_self32, Nat.sub_zero, ofNat_toNat32]
  -- The registers restored, and the blocks as the contract says.
  obtain fin : ∀ u, LInv s m0 up S D (Spec.Cast5.scheduleAt s.mem (K.setWidth 64)) R.toNat N.toNat N.toNat u →
      WP isa (.block restore) u fun s' => abiPreserved s s' ∧ (ecbX up).post s s' := by
    intro u hu
    obtain hd := loopMem_disjoint hl
    obtain hs0 : Spill.Saved SM (addr S) g saved := Spill.saveMem_saved_addr s.mem g saved_fits fitS
    obtain hs1 : Spill.Saved m0 (addr S) g saved :=
      hs0.of_frame (argMem_frame SM fitS K R D N) (saved_contains fitS) fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by decide) (by decide) (by decide)
    obtain hs2 : Spill.Saved u.mem (addr S) g saved :=
      hs1.of_frame hu.fr (saved_contains fitS) fun r hr =>
        ((hd r hr).2.2.symm).sub_left (Offset.sub _ (by decide) (by decide))
    rw [restore_eq, saved_eq, ← List.append_nil (Spill.restoreCode _ _)]
    refine Spill.restoreBase_ok savedL (by decide) (fun p hp => ?_) (by rw [hu.si, ← saved_eq]; exact hs2)
      fun s' hr => WP.block_nil ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
    · rw [hu.si, hu.rd, hu.wr]
      rw [← saved_eq] at hp
      exact slot_rd fitS wS (d := p.2) (n := 4) (by have := saved_fits.1 p hp; omega_arith)
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl
      · exact (hr.gpr (.ebx, savedOff) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
      · exact (hr.gpr (.esi, savedOff + 4) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
      · exact (hr.gpr (.edi, savedOff + 8) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
      · exact (hr.gpr (.ebp, savedOff + 12) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
      · exact (hr.other .esp (by decide)).trans hu.sp
    · have dR : ∀ r ∈ loopMem S D N.toNat (s.gpr .esp), Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r := by
        intro r hr'
        simp only [loopMem, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl
        · rw [← hD, ← hN]; exact h.dRD
        · rw [← hS]; exact h.dRS.sub_right (by rw [hS]; exact slot_sub S (by decide))
        · rw [← hS]; exact h.dRS.sub_right (by rw [hS]; exact slot_sub S (by decide))
        · rw [below, Taint.sub_setWidth h.sp]
          exact Offset.base_disjoint_below _ (by decide)
      rw [hr.mem, hu.fr.readW (Region.contains_self _ _) dR (by decide),
        F.readW (Region.contains_self _ _) (dF _ (by rw [← hS]; exact h.dRS)) (by decide)]
    · show Spec.Cast5.blocksAt s'.mem _ _ = _
      rw [hK, hR, hD, hN, hr.mem, ← cipher_map]
      unfold Spec.Cast5.blocksAt
      rw [List.map_map]
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      simp only [Function.comp]
      rw [hu.blocks i hi, ite_eq_left hi, blockAt_frame F fun r hr' => by
        rw [List.mem_singleton] at hr'; subst hr'
        exact (show Region.Disjoint ⟨D.setWidth 64, 8 * N.toNat⟩ ⟨S.setWidth 64, 256⟩ by
          rw [← hD, ← hN, ← hS]; exact h.dDS).sub_left (sub_blk _ hi)]
  refine WP.seq (WP.mono (Q := LInv s m0 up S D (Spec.Cast5.scheduleAt s.mem (K.setWidth 64)) R.toNat N.toNat N.toNat)
    ?_ fin)
  obtain hz : isa.eval .e s₃ = some (decide (N.toNat = 0)) := by
    simp only [eval, z₃, BitVec.sub_zero]
    congr 1
  refine WP.ite (decide (N.toNat = 0)) hz (fun hN0 => ?_) (fun hN0 => ?_)
  · have e : N.toNat = 0 := of_decide_eq_true hN0
    refine WP.block_nil ?_
    rw [e]; rw [e] at h0; exact h0
  · exact ecbLoop_ok hl (by have := of_decide_eq_false hN0; omega_arith) h0

end VG.Proof.Cast5.X86
