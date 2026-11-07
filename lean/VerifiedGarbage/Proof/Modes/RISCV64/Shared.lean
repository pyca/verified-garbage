module

public import VerifiedGarbage.Impl.Modes.RISCV64.Shared
public import VerifiedGarbage.Proof.Modes.RISCV64.Core
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Covers

/-! # Sharing a verified RISC-V mode core through internal calls -/

@[expose] public section

namespace VG.Proof.Modes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Modes.RISCV64

/-- Each region of `rs` is within one of `ts`. -/
def Within (rs ts : List Region) : Prop := ∀ r ∈ rs, ∃ t ∈ ts, Region.Sub r t

theorem Within.refl (rs : List Region) : Within rs rs := fun r hr => ⟨r, hr, fun _ h => h⟩

theorem addrStep_wp {s : State} {B : Addr} {n a : Nat}
    (hB : s.gpr .t6 = B + BitVec.ofNat 64 a) (h : a ≤ 8 * n + 2048 ∧ 8 * n < a + 2048) :
    WP isa (.block [.addi .t6 .t6 ((8 * n : Int) - a)]) s fun u =>
      Upd s u .t6 (B + BitVec.ofNat 64 (8 * n)) := by
  by_cases hn : a ≤ 8 * n
  · rw [show (8 * n : Int) - a = (8 * n - a : Nat) by omega]
    refine wp_addi (by omega) fun u hu => WP.block_nil ?_
    have e : s.gpr .t6 + BitVec.ofNat 64 (8 * n - a) = B + BitVec.ofNat 64 (8 * n) := by
      rw [hB, Offset.add_add]; congr 2; omega
    exact e ▸ hu
  · rw [show (8 * n : Int) - a = -((a - 8 * n : Nat) : Int) by omega]
    refine wp_subi (by omega) fun u hu => WP.block_nil ?_
    have e : s.gpr .t6 - BitVec.ofNat 64 (a - 8 * n) = B + BitVec.ofNat 64 (8 * n) := by
      rw [hB, show BitVec.ofNat 64 a = BitVec.ofNat 64 (8 * n) + BitVec.ofNat 64 (a - 8 * n) by
        rw [← BitVec.ofNat_add]; congr 1; omega, ← BitVec.add_assoc, BitVec.add_sub_cancel]
    exact e ▸ hu

theorem returnAddr_wp {s : State} {B : Addr} {n : Nat} (hB : s.gpr sb = B) (hn : n ≤ 761) :
    WP isa (.block (returnAddr n)) s fun u => Upd s u .t6 (B + BitVec.ofNat 64 (8 * n)) := by
  unfold returnAddr
  split
  · rename_i h
    refine wp_addi (by decide) fun a ha => WP.mono (addrStep_wp (n := n) (a := 2032) (ha.gpr.trans (by rw [hB])) (by omega)) ?_
    intro u hu
    exact ⟨hu.gpr, fun r hr => by rw [hu.other r hr, ha.other r hr],
      hu.mem.trans ha.mem, hu.rd.trans ha.rd, hu.wr.trans ha.wr, hu.sp.trans ha.sp⟩
  · rename_i h
    refine wp_addi (by decide) fun a ha => wp_addi (by decide) fun b hb => ?_
    have eb : b.gpr .t6 = B + BitVec.ofNat 64 4064 := by
      rw [hb.gpr, ha.gpr, hB, Offset.add_add]
    refine WP.mono (addrStep_wp (n := n) (a := 4064) eb (by omega)) fun u hu => ?_
    exact ⟨hu.gpr, fun r hr => by rw [hu.other r hr, hb.other r hr, ha.other r hr],
      by rw [hu.mem, hb.mem, ha.mem], by rw [hu.rd, hb.rd, ha.rd],
      by rw [hu.wr, hb.wr, ha.wr], by rw [hu.sp, hb.sp, ha.sp]⟩

/-- What remains of the caller on entry to the shared core. -/
structure SharedInput (s t : State) (B : Addr) (n : Nat) : Prop where
  regs : ∀ r ∈ kept, r ≠ .ra → t.gpr r = s.gpr r
  mem : t.mem = s.mem.writeW (slotA B n) (s.gpr .ra)
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- The callee's result after the caller's return address is restored. -/
structure SharedOutput (s u v : State) : Prop where
  regs : ∀ r, r ≠ .ra → r ≠ .t6 → v.gpr r = u.gpr r
  ra : v.gpr .ra = s.gpr .ra
  mem : v.mem = u.mem
  rd : v.rd = s.rd
  wr : v.wr = s.wr

/-- Running an unchanged core body through a call. The body's frame
keeps the saved return address outside the original core's slots. -/
theorem sharedCall_wp {c : Core} (hc : Layout c) (hn : c.total ≤ 761)
    {name : String} {body : Prog isa}
    {s : State} {B : Addr} (hB : s.gpr sb = B) (hS : ScrIn s B (c.total + 2))
    {P : State → State → Prop}
    (hbody : ∀ t, SharedInput s t B c.total →
      WP isa body t fun u => (∀ r ∈ kept, u.gpr r = t.gpr r) ∧
        Frame [coreRegion c B] t.mem u.mem ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ P t u) :
    WP isa (sharedCall name body c.total) s fun v =>
      ∃ t u, SharedInput s t B c.total ∧ (∀ r ∈ kept, u.gpr r = t.gpr r) ∧
        Frame [coreRegion c B] t.mem u.mem ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ P t u ∧ SharedOutput s u v := by
  have hn' : 8 * c.total + 8 ≤ 8 * (c.total + 2) := by omega
  have hal : (slotA B c.total).toNat % 8 = 0 :=
    Spill.al8 (by have := hS.al; omega) (by omega)
  have hin : InRegions s.wr (slotA B c.total) 8 :=
    hS.wr _ _ (by decide) hn' (by have := hc.even; omega)
  have hcore : Region.Sub (coreRegion c B) ⟨B, 8 * c.total⟩ :=
    Offset.sub_base B (by have := hc.buf_ge; have := hc.buf_le; omega)
  have hdis : Region.Disjoint ⟨slotA B c.total, 8⟩ (coreRegion c B) :=
    (Offset.disjoint_base B (by omega) (by omega)).sub_right hcore
  unfold sharedCall
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (returnAddr_wp hB hn) fun a ha => ?_
  refine wp_sd (a := slotA B c.total) (by decide) (by rw [ha.gpr, BitVec.add_zero]) hal
    (by rw [ha.wr]; exact hin) fun b hb => WP.block_nil ?_
  let t := b.callEntry
  have hi : SharedInput s t B c.total := by
    refine ⟨fun r hr hra => ?_, ?_, hb.rd.trans ha.rd, hb.wr.trans ha.wr⟩
    · rw [State.callEntry_gpr _ (by
        simp only [kept, List.mem_cons] at hr
        rcases hr with rfl | rfl | hr
        · decide
        · exact absurd rfl hra
        · exact preserved_not_link r hr), hb.gpr, ha.other r (by
          intro e; subst e; exact absurd hr (by decide))]
    · change b.mem = _
      rw [hb.mem, ha.mem, ha.other .ra (by decide)]
  have hw := hbody t hi
  obtain ⟨tr, u, eu, ku, fu, rdu, wru, pu⟩ := hw
  have retu : isa.ret t u = some u := by
    simp only [isa, ret]; exact ite_eq_left (ku .ra (by decide))
  refine WP.seq ⟨_, u, Exec.call (call_callEntry b) eu retu, ?_⟩
  have huB : u.gpr sb = B := (ku _ (by decide)).trans ((hi.regs _ (by decide) (by decide)).trans hB)
  have hum : u.mem.readW (slotA B c.total) 64 = s.gpr .ra := by
    rw [fu.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hdis) (by decide), hi.mem,
      Mem.readW_writeW_self64]
  change WP isa (.block (returnAddr c.total ++ [.load .d .ra .t6 0])) u _
  rw [WP.block_append_iff]
  refine WP.mono (returnAddr_wp huB hn) fun d hd => ?_
  refine wp_ld (a := slotA B c.total) (by decide) (by rw [hd.gpr, BitVec.add_zero]) hal
    (by rw [hd.rd, hd.wr, rdu, wru, hi.rd, hi.wr]
        obtain ⟨r, hr, hc⟩ := hin; exact ⟨r, List.mem_append_right _ hr, hc⟩) fun v hv => WP.block_nil ?_
  refine ⟨t, u, hi, ku, fu, rdu, wru, pu, ⟨fun r hra ht6 => by rw [hv.other r hra, hd.other r ht6],
    ?_, hv.mem.trans hd.mem, by rw [hv.rd, hd.rd, rdu, hi.rd], by rw [hv.wr, hd.wr, wru, hi.wr]⟩⟩
  rw [hv.gpr, hd.mem, hum]

/-- The original core gets a single region for its frame when it needs one.
Larger frames already have the chunked permissions its proofs use.
`original_scr` excludes cores whose added slots cross the 4064-byte
single-allocation boundary. -/
def originalWr (c : Core) (B : Addr) (wr : List Region) : List Region :=
  if c.total ≤ 506 then ⟨B, 8 * c.total⟩ :: wr else wr

def originalState (c : Core) (s : State) (B : Addr) : State :=
  s.withRegions s.rd (originalWr c B s.wr)

theorem original_scr {c : Core} {s : State} {B : Addr}
    (hn : c.total ≤ 506 ∨ 508 < c.total) (hS : ScrIn s B (c.total + 2)) :
    ScrIn (originalState c s B) B c.total := by
  have low : ∀ o w, o + w ≤ min (8 * c.total) 2032 → InRegions s.wr (B + BitVec.ofNat 64 o) w :=
    fun o w h => hS.low o w (by omega)
  refine ⟨hS.al, by have := hS.fit; omega, fun o w h => ?_, fun h => ?_, fun o w hp hq hr => ?_⟩
  · unfold originalState originalWr; split
    · obtain ⟨r, hr, hc⟩ := low o w h; exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
    · exact low o w h
  · have hsmall : c.total ≤ 506 := by omega
    simp only [originalState, State.withRegions_wr, originalWr, ite_eq_left hsmall]
    exact List.mem_cons_self
  · unfold originalState originalWr; split
    · obtain ⟨r, hr', hc⟩ := hS.wr o w hp (by omega) hr
      exact ⟨r, List.mem_cons_of_mem _ hr', hc⟩
    · exact hS.wr o w hp (by omega) hr

theorem original_covers {c : Core} {s : State} {B : Addr} (hS : ScrIn s B (c.total + 2)) :
    Covers (originalWr c B s.wr) s.wr := by
  unfold originalWr; split
  · rename_i h
    refine Covers.cons ?_ (Covers.refl _)
    exact Covers.one ⟨_, hS.whole (by omega), by
      simpa only [BitVec.add_zero] using Offset.contains_base B (d := 0) (n := 8 * c.total)
        (k := 8 * (c.total + 2)) (by omega) (by decide)⟩
  · exact Covers.refl _

theorem original_extra (c : Core) (s : State) (B : Addr) :
    ∃ ws, (originalState c s B).wr = ws ++ s.wr := by
  unfold originalState originalWr; split
  · exact ⟨[_], rfl⟩
  · exact ⟨[], rfl⟩

/-- Readiness remembers a set of regions covering the larger caller's
frame. Keeping the original permissions makes this valid even when the
original core's readiness mentions readable memory. -/
def SharedReady {c : Core} (cs : CoreSpec c) (s : State) (B : Addr) (ws : List Region) (k : cs.Key) : Prop :=
  ∃ rs, Within (⟨B, 8 * (c.total + 2)⟩ :: ws) rs ∧ cs.Ready (originalState c s B) B rs k

/-- The two additional slots are after the original core's slots. -/
theorem shared_core_sub {c : Core} (B : Addr) (pn cn) :
    Region.Sub (coreRegion c B) (coreRegion (c.shared pn cn) B) := by
  exact Region.sub_prefix (by simp only [Core.shared]; omega)

theorem shared_layout {c : Core} (hc : Layout c) (hn : c.total ≤ 761) (pn cn) : Layout (c.shared pn cn) :=
  ⟨hc.G_pos, hc.bw, hc.buf_ge, by have := hc.buf_le; simpa only [Core.shared] using (by omega :
      8 * c.buf + 4 * c.bw * c.G ≤ 8 * (c.total + 2)),
    hc.disp, by have := hc.even; dsimp only [Core.shared]; omega,
    by simp only [Core.shared]; omega⟩

/-- The key's arguments depend on the key pointer and memory, and can be
restricted to subregions of the caller's writable regions. -/
def KeyMove {c : Core} (cs : CoreSpec c) : Prop :=
  ∀ {s t rs ts k}, cs.KeyArgs s rs k → t.gpr .a0 = s.gpr .a0 → t.rd = s.rd →
    (∃ extra, t.wr = extra ++ s.wr) → Frame rs s.mem t.mem → Within ts rs → cs.KeyArgs t ts k

/-- Readiness depends on the key pointer, permissions and memory. -/
def ReadyMove {c : Core} (cs : CoreSpec c) : Prop :=
  ∀ {s t B ws k rs}, cs.Ready s B ws k → t.gpr .a0 = s.gpr .a0 → t.rd = s.rd → t.wr = s.wr →
    Frame rs s.mem t.mem → Within rs ws →
    (∀ r ∈ rs, Region.Disjoint (coreRegion c B) r ∨ Region.Sub r (blkRegion c B)) → cs.Ready t B ws k

theorem SharedInput.frame {s t B n} (hi : SharedInput s t B n) :
    Frame [⟨slotA B n, 8⟩] s.mem t.mem := by
  rw [hi.mem]
  exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)

theorem saved_sub (c : Core) (hc : Layout c) (B : Addr) (pn cn) :
    Region.Sub ⟨slotA B c.total, 8⟩ (coreRegion (c.shared pn cn) B) := by
  exact Offset.sub B (by have := hc.buf_ge; have := hc.buf_le; omega) (by simp only [Core.shared]; omega)

theorem SharedOutput.kept {s t u v B n} (hi : SharedInput s t B n)
    (hu : ∀ r ∈ kept, u.gpr r = t.gpr r) (hv : SharedOutput s u v) :
    ∀ r ∈ kept, v.gpr r = s.gpr r := by
  intro r hr
  by_cases hra : r = .ra
  · subst hra; exact hv.ra
  · rw [hv.regs r hra (by intro e; subst e; exact absurd hr (by decide)), hu r hr, hi.regs r hr hra]

namespace CoreSpec

variable {c : Core} (cs : CoreSpec c) (hn : c.total ≤ 761) (hg : c.total ≤ 506 ∨ 508 < c.total)
    (hkey : KeyMove cs) (hready : ReadyMove cs) (hpn : c.prepare.noFrames = true) (hcn : c.crypt.noFrames = true)
    (pn cn : String)

include hready in
/-- Restoring the link and temporary registers does not affect readiness. -/
theorem output_ready {s u v : State} {B : Addr} {ws : List Region} {k : cs.Key}
    (hr : SharedReady cs u B ws k) (hv : SharedOutput s u v)
    (ha : v.gpr .a0 = u.gpr .a0) (rd : u.rd = s.rd) (wr : u.wr = s.wr) :
    SharedReady cs v B ws k := by
  obtain ⟨rs, hs, hr⟩ := hr
  refine ⟨rs, hs, hready hr ha (hv.rd.trans rd.symm) ?_ (by change Frame [] u.mem v.mem; rw [hv.mem]; exact Frame.refl _ _)
    (fun r h => absurd h List.not_mem_nil) (fun r h => absurd h List.not_mem_nil)⟩
  change originalWr c B v.wr = originalWr c B u.wr
  rw [hv.wr, wr]

include hn hg hkey hready hpn in
/-- The shared preparation meets the original core's contract. -/
theorem shared_prepare {s : State} {B : Addr} {rs : List Region} {k : cs.Key}
    (hB : s.gpr sb = B) (hS : ScrIn s B (c.total + 2))
    (hm : (⟨B, 8 * (c.total + 2)⟩ : Region) ∈ rs) (hk : cs.KeyArgs s rs k) :
    WP isa (c.shared pn cn).prepare s fun v => SharedReady cs v B rs k ∧ v.gpr sb = B ∧
      (∀ r ∈ kept, v.gpr r = s.gpr r) ∧ Frame [coreRegion (c.shared pn cn) B] s.mem v.mem ∧
      v.rd = s.rd ∧ v.wr = s.wr := by
  refine WP.mono (sharedCall_wp cs.layout hn hB hS (P := fun _ u =>
    cs.Ready (originalState c u B) B (⟨B, 8 * c.total⟩ :: rs) k) ?_) ?_
  · intro t hi
    have hsT : ScrIn t B (c.total + 2) := hS.congr hi.wr
    have hK : cs.KeyArgs (originalState c t B) (⟨B, 8 * c.total⟩ :: rs) k :=
      hkey hk (hi.regs _ (by decide) (by decide)) hi.rd
        (by obtain ⟨extra, he⟩ := original_extra c t B; exact ⟨extra, he.trans (by rw [hi.wr])⟩)
        (hi.frame.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨_, hm, Offset.sub_base B (by omega)⟩)
        (fun r hr => by
          rcases List.mem_cons.mp hr with he | hr
          · subst he; exact ⟨_, hm, Region.sub_prefix (by omega)⟩
          · exact ⟨_, hr, fun _ h => h⟩)
    have htB : (originalState c t B).gpr sb = B := (hi.regs _ (by decide) (by decide)).trans hB
    have raw := cs.prepare_wp htB (original_scr hg hsT) List.mem_cons_self hK
    refine WP.narrow raw (Covers.append (Covers.refl _) (original_covers hsT)) (original_covers hsT)
      (fun u rd wr _ _ ⟨hr, _, ku, fu, _, _⟩ => ?_) hpn
    refine ⟨ku, fu, rd, wr, ?_⟩
    simpa only [originalState, rd, wr] using hr
  · intro v ⟨t, u, hi, ku, fu, rd, wr, hr, hv⟩
    have ready : SharedReady cs u B rs k := ⟨⟨B, 8 * c.total⟩ :: rs, fun r h => by
      rcases List.mem_cons.mp h with he | h
      · subst he; exact ⟨_, List.mem_cons_of_mem _ hm, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ h, fun _ h => h⟩, hr⟩
    have kk := hv.kept hi ku
    refine ⟨output_ready cs hready ready hv (hv.regs _ (by decide) (by decide))
        (rd.trans hi.rd) (wr.trans hi.wr), (kk _ (by decide)).trans hB, kk, ?_, hv.rd, hv.wr⟩
    rw [hv.mem]
    exact (hi.frame.sub fun r h => by
      simp only [List.mem_singleton] at h; subst h
      exact ⟨_, List.mem_singleton_self _, saved_sub c cs.layout B pn cn⟩).trans
      (fu.sub fun r h => by
        simp only [List.mem_singleton] at h; subst h
        exact ⟨_, List.mem_singleton_self _, shared_core_sub B pn cn⟩)

include hn hg hready hcn in
/-- The shared batch meets the original core's contract. -/
theorem shared_crypt {s : State} {B : Addr} {ws : List Region} {k : cs.Key}
    (hB : s.gpr sb = B) (hS : ScrIn s B (c.total + 2)) (hr : SharedReady cs s B ws k) :
    WP isa (c.shared pn cn).crypt s fun v => v.gpr sb = B ∧
      (∀ r ∈ kept, v.gpr r = s.gpr r) ∧ SharedReady cs v B ws k ∧
      Frame [coreRegion (c.shared pn cn) B] s.mem v.mem ∧
      (∀ j < c.G, Spec.Aes.bytesAt v.mem (blkAddr c B j) (4 * c.bw) =
        cs.cipher k (Spec.Aes.bytesAt s.mem (blkAddr c B j) (4 * c.bw))) ∧ v.rd = s.rd ∧ v.wr = s.wr := by
  obtain ⟨rs, hrs, hr⟩ := hr
  refine WP.mono (sharedCall_wp cs.layout hn hB hS (P := fun t u =>
    cs.Ready (originalState c u B) B rs k ∧
      ∀ j < c.G, Spec.Aes.bytesAt u.mem (blkAddr c B j) (4 * c.bw) =
        cs.cipher k (Spec.Aes.bytesAt t.mem (blkAddr c B j) (4 * c.bw))) ?_) ?_
  · intro t hi
    have hsT : ScrIn t B (c.total + 2) := hS.congr hi.wr
    have hrT : cs.Ready (originalState c t B) B rs k :=
      hready hr (hi.regs _ (by decide) (by decide)) hi.rd
        (by change originalWr c B t.wr = originalWr c B s.wr; rw [hi.wr]) hi.frame
        (fun r h => by
          simp only [List.mem_singleton] at h; subst h
          obtain ⟨r', hr', sub⟩ := hrs _ List.mem_cons_self
          exact ⟨r', hr', fun x hx => sub x ((Offset.sub_base B (d := 8 * c.total)
            (n := 8) (k := 8 * (c.total + 2)) (by omega)) x hx)⟩)
        (fun r h => by
          simp only [List.mem_singleton] at h; subst h
          exact .inl ((Offset.disjoint_base B (d := 8 * c.total) (n := 8) (k := 8 * c.total)
            (by omega) (by omega)).symm.sub_left
            (Offset.sub_base B (by have := cs.layout.buf_ge; have := cs.layout.buf_le; omega))))
    have htB : (originalState c t B).gpr sb = B := (hi.regs _ (by decide) (by decide)).trans hB
    have raw := cs.crypt_wp htB (original_scr hg hsT) hrT
    refine WP.narrow raw (Covers.append (Covers.refl _) (original_covers hsT)) (original_covers hsT)
      (fun u rd wr _ _ ⟨_, ku, hr, fu, bl, _, _⟩ => ?_) hcn
    refine ⟨ku, fu, rd, wr, ?_, bl⟩
    simpa only [originalState, rd, wr] using hr
  · intro v ⟨t, u, hi, ku, fu, rd, wr, ⟨hr, bl⟩, hv⟩
    have kk := hv.kept hi ku
    refine ⟨(kk _ (by decide)).trans hB, kk,
      output_ready cs hready ⟨rs, hrs, hr⟩ hv (hv.regs _ (by decide) (by decide))
        (rd.trans hi.rd) (wr.trans hi.wr), ?_, ?_, hv.rd, hv.wr⟩
    · rw [hv.mem]
      exact (hi.frame.sub fun r h => by
        simp only [List.mem_singleton] at h; subst h
        exact ⟨_, List.mem_singleton_self _, saved_sub c cs.layout B pn cn⟩).trans
        (fu.sub fun r h => by
          simp only [List.mem_singleton] at h; subst h
          exact ⟨_, List.mem_singleton_self _, shared_core_sub B pn cn⟩)
    · intro j hj
      have hjlen : 4 * c.bw * j + 4 * c.bw ≤ 4 * c.bw * c.G := by
        simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (4 * c.bw) (Nat.succ_le_of_lt hj)
      rw [hv.mem, bl j hj]
      congr 1
      apply List.ext_getElem
      · simp only [Spec.Aes.bytesAt, List.length_map, List.length_range]
      · intro i hil hir
        have hi' : i < 4 * c.bw := by simpa only [Spec.Aes.bytesAt, List.length_map, List.length_range] using hil
        simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range]
        refine hi.frame.bytes (R := ⟨blkAddr c B j, 4 * c.bw⟩) (fun r h => ?_)
          (by change 4 * c.bw ≤ 2 ^ 64; have := cs.layout.disp; omega) hi'
        simp only [List.mem_singleton] at h; subst h
        unfold blkAddr slotA
        rw [Offset.add_add]
        exact Offset.disjoint B (.inl (by have := cs.layout.buf_le; omega))
          (by have := cs.layout.disp; omega) (by omega)

include hn hg hkey hready hpn hcn in
/-- Share any core whose key and readiness obey the stronger congruences
above. No trusted model or public cryptographic contract changes. -/
def shared : CoreSpec (c.shared pn cn) where
  Key := cs.Key
  cipher := cs.cipher
  KeyArgs := cs.KeyArgs
  Ready := SharedReady cs
  cipher_len := cs.cipher_len
  layout := shared_layout cs.layout hn pn cn
  keyArgs_congr := cs.keyArgs_congr
  ready_frame {s t B ws k rs} hr hk rd wr sy fr hs hd := by
    obtain ⟨rawrs, cover, hr⟩ := hr
    refine ⟨rawrs, cover, hready hr hk.a0 rd ?_ fr ?_ ?_⟩
    · change originalWr c B t.wr = originalWr c B s.wr; rw [wr]
    · intro r h
      obtain ⟨r', hr', sub⟩ := hs r h
      obtain ⟨r'', hr'', sub'⟩ := cover r' (List.mem_cons_of_mem _ hr')
      exact ⟨r'', hr'', fun x hx => sub' x (sub x hx)⟩
    · intro r h
      rcases hd r h with hd | hd
      · exact .inl (hd.sub_left (shared_core_sub B pn cn))
      · exact .inr hd
  prepare_wp := shared_prepare cs hn hg hkey hready hpn pn cn
  crypt_wp := shared_crypt cs hn hg hready hcn pn cn

end CoreSpec

end VG.Proof.Modes.RISCV64
