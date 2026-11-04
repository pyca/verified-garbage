module

public import VerifiedGarbage.Proof.RsaPss.AArch64.MgfParts
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfT
public import VerifiedGarbage.Proof.RsaPss.AArch64.TabCall
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.RsaPss.AArch64.CtHash
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Encode
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# RSASSA-PSS on AArch64: MGF1

`mgfXor` XORs `MGF1(H, dbLen)` into `DB`, where `H` is the `hLen` bytes after
`DB` (`mgfXor_ok`), with MGF1's hash function `G` that of the table of `Hash`
whose address is in the slot `sMgfT`: it is OAEP's MGF1 with a table
(`Proof/RsaOaep/AArch64/MgfT.lean`), in a frame of its own of OAEP's layout
(`mgfFrame`) below ours, with `scratch + mgfOff` as its working space
(`Env`: where it works, and the table). Its working space writes only
OAEP's ranges for the hash function (`hashR`), which are in `Y`, and `DB`
(`mgf_frame`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_strx eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp setWidth_ofNat16)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss (getD_app i2osp_len mgf1_getD)

/-- `DB` with the first `n` bytes of the mask `mk` XORed in. -/
def mixV (V : Nat → Byte) (mk : List Byte) (e n : Nat) (o : Nat) : Byte :=
  if e ≤ o ∧ o < e + n then V o ^^^ mk.getD (o - e) 0 else V o

/-- What `mgfXor`, and the code around it, may write: our working space, the
stack below the frame (MGF1's frame and what its callees use), and two
slots. -/
abbrev mgfWr (F S : Addr) : List Region :=
  [⟨S, oRsa⟩, below F 16, slotR F sNb, slotR F sDone, below F (mgfFrame + 16)]

theorem slot_keep {F : Addr} {d : Nat} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (slotR F d) r) :
    m'.readW (off F d) 64 = m.readW (off F d) 64 :=
  hf.readW (r := slotR F d) (Region.contains_self _ _) hd (by decide)

theorem Lay.doneD {t : State} {F S : Addr} (L : Lay t F S) :
    ∀ r ∈ [(⟨S, oRsa⟩ : Region), below F 16, slotR F sNb], Region.Disjoint (slotR F sDone) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.dFS.sub_left (Offset.sub_base F (by decide))
  · exact slot_not_below F (by decide)
  · exact Offset.disjoint F (by decide) (by decide) (by decide)

theorem byte_of_bytesAt {m : Mem} {p : Addr} {n : Nat} {xs : List Byte} (h : Spec.Rsa.bytesAt m p n = xs)
    {k : Nat} (hk : k < n) : m (p + BitVec.ofNat 64 k) = xs.getD k 0 := by
  subst h
  simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-! ## Where MGF1 works -/

/-- What MGF1 needs of where it runs, from the state `t` with our frame at
`F` and our working space at `S`: its working space writable; its frame,
and the stack below it, apart from its working space and above address 0;
and the table of `Hash` at `p` (whose address is in the slot `sMgfT`),
readable, holding the addresses of `G`'s functions (which the calls of `g`
reach) and its digest length in every memory MGF1 may leave. -/
structure Env (G : Impl.Pbkdf2.Md.AArch64.Stream) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) (t : State)
    (F S p : Addr) : Prop where
  slot : t.mem.readW (off F sMgfT) 64 = p
  ok : Proof.RsaOaep.AArch64.Table.TabOK G g t.syms
  rd : ∀ j < 3, InRegions (t.rd ++ t.wr) (off p (8 * j)) 8
  rdD : InRegions (t.rd ++ t.wr) (off p 32) 8
  mem : ∀ m, Frame (mgfWr F S ++ [⟨off S mgfOff, 8192⟩]) t.mem m →
    Proof.RsaOaep.AArch64.Table.TabMem G t.syms p m ∧ m.readW (off p 32) 64 = BitVec.ofNat 64 G.D
  sc : Covers [⟨off S mgfOff, 8192⟩] t.wr
  F288 : mgfFrame + 16 ≤ F.toNat
  dStk : Region.Disjoint (below F (mgfFrame + 16)) ⟨off S mgfOff, 8192⟩
  Sw : (off S mgfOff).toNat + 8192 ≤ 2 ^ 64
  dFw : Region.Disjoint ⟨F, frameBytes⟩ ⟨off S mgfOff, 8192⟩

theorem mgfFrame_eq : mgfFrame = 272 := rfl

/-- MGF1's frame, below ours. -/
abbrev mF (F : Addr) : Addr := F - BitVec.ofNat 64 mgfFrame

theorem mF_toNat {F : Addr} (h : mgfFrame + 16 ≤ F.toNat) : (mF F).toNat = F.toNat - 272 := by
  simp only [mF, BitVec.toNat_sub, BitVec.toNat_ofNat, mgfFrame_eq] at *; omega

theorem sub_mF (F : Addr) : Region.Sub ⟨mF F, 272⟩ (below F (mgfFrame + 16)) :=
  Offset.sub_below F (a := 272) (b := 288) (by decide) (by decide)

theorem sub_retR (F : Addr) : Region.Sub (Proof.RsaOaep.AArch64.retR (mF F)) (below F (mgfFrame + 16)) := by
  have e : mF F - BitVec.ofNat 64 16 = F - BitVec.ofNat 64 288 := by
    simp only [mF, mgfFrame_eq, BitVec.sub_sub, BitVec.ofNat_add_ofNat]
  simp only [Proof.RsaOaep.AArch64.retR, below, e]
  exact Offset.sub_below F (a := 288) (b := 288) (by decide) (by decide)

theorem Env.geo {G : Impl.Pbkdf2.Md.AArch64.Stream} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {t : State}
    {F S p : Addr} (E : Env G g t F S p) : Proof.RsaOaep.AArch64.Geo (mF F) (off S mgfOff) where
  F16 := by rw [mF_toNat E.F288]; have := E.F288; rw [mgfFrame_eq] at this; omega
  Fw := by rw [mF_toNat E.F288]; have := E.F288; have := F.isLt; unfold Impl.RsaOaep.AArch64.frameBytes; omega
  Sw := E.Sw
  dFS := E.dStk.sub_left (sub_mF F)
  dRS := E.dStk.sub_left (sub_retR F)
  dRF := by
    have h := Offset.disjoint (mF F - BitVec.ofNat 64 16) (d := 0) (n := 16) (e := 16) (k := 272) (by omega)
      (by omega) (by omega)
    rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero, BitVec.sub_add_cancel] at h

/-- A slot apart from what `mgfWr` writes. -/
theorem Lay.slotW {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (hd : d + 8 ≤ frameBytes)
    (h1 : d + 8 ≤ sNb ∨ sNb + 8 ≤ d) (h2 : d + 8 ≤ sDone ∨ sDone + 8 ≤ d) :
    ∀ r ∈ mgfWr F S, Region.Disjoint (slotR F d) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.dFS.sub_left (Offset.sub_base F hd)
  · exact slot_not_below F hd
  · exact Offset.disjoint F h1 (by unfold frameBytes at hd; omega_using [hd]) (by decide)
  · exact Offset.disjoint F h2 (by unfold frameBytes at hd; omega_using [hd]) (by decide)
  · exact Offset.disjoint_below F (by have := L.Fw; unfold frameBytes at hd; rw [mgfFrame_eq]; omega)

/-- `Env` in a later state, after writes `mgfWr` allows. -/
theorem Env.step {G : Impl.Pbkdf2.Md.AArch64.Stream} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {t u : State}
    {F S p : Addr} (E : Env G g t F S p) (L : Lay t F S) (hf : Frame (mgfWr F S) t.mem u.mem) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) (hsy : u.syms = t.syms) : Env G g u F S p where
  slot := by rw [slot_keep hf (L.slotW (d := sMgfT) (by decide) (by decide) (by decide))]; exact E.slot
  ok := by rw [hsy]; exact E.ok
  rd := by rw [hrd, hwr]; exact E.rd
  rdD := by rw [hrd, hwr]; exact E.rdD
  mem := fun m hm => by rw [hsy]; exact E.mem m ((hf.mono (by simp)).trans hm)
  sc := by rw [hwr]; exact E.sc
  F288 := E.F288
  dStk := E.dStk
  Sw := E.Sw
  dFw := E.dFw

/-- The slots of the table of `MdHash` in a later state. -/
theorem HT.stepW {H : Hash} {dn : String} {f : MdFns} {t : State} {F S : Addr} (L : Lay t F S) {m m' : Mem}
    {sy : String → Addr} (h : HT H dn f F m sy) (hf : Frame (mgfWr F S) m m') : HT H dn f F m' sy :=
  ⟨by rw [slot_keep hf (L.slotW (d := sIniH) (by decide) (by decide) (by decide))]; exact h.wi,
    by rw [slot_keep hf (L.slotW (d := sCmpH) (by decide) (by decide) (by decide))]; exact h.wc,
    by rw [slot_keep hf (L.slotW (d := sDigH) (by decide) (by decide) (by decide))]; exact h.wd, h.fi, h.fc, h.fd⟩

/-! ## MGF1's arguments -/

/-- The five words of MGF1's slots. -/
def argsMem (a : State) (F' : Addr) (D : Nat) : Mem :=
  ((((a.mem.writeW (off F' 96) (a.gpr .x20 + BitVec.ofNat 64 mgfOff)).writeW (off F' 104)
    (a.gpr .x24 + a.gpr .x25)).writeW (off F' 112) (BitVec.ofNat 64 D)).writeW (off F' 120)
    (a.gpr .x24)).writeW (off F' 128) (a.gpr .x25)

theorem args_ok (H : Hash) (hD : H.D < 65536) {a : State} {F' : Addr} (hsp : a.sp = F')
    (hw : ∀ d, d + 8 ≤ 272 → InRegions a.wr (off F' d) 8) :
    WP isa (.block (mgfArgs H)) a fun u => Keep [.x9, .x10] a u ∧ u.mem = argsMem a F' H.D := by
  unfold mgfArgs movi
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun u₂ o₂ e₂ => ?_
  have x9 : u₂.gpr .x9 = F' := by rw [o₂.get .x9, e₁, hsp, BitVec.add_zero]
  have w : ∀ (u : State), u.wr = a.wr → ∀ d, d + 8 ≤ 272 → InRegions u.wr (off F' d) 8 := fun u h d hd => by
    rw [h]; exact hw d hd
  refine wp_strx (by decide) (by rw [x9]; rfl) (w _ (by rw [o₂.wr, o₁.wr]) 96 (by decide)) fun u₃ m₃ => ?_
  refine VG.Proof.MlKem.AArch64.wp_add fun u₄ o₄ e₄ => ?_
  refine wp_strx (by decide) (by rw [o₄.get .x9, m₃.gpr, x9]; rfl)
    (w _ (by rw [o₄.wr, m₃.wr, o₂.wr, o₁.wr]) 104 (by decide)) fun u₅ m₅ => ?_
  refine wp_movz fun u₆ o₆ e₆ => ?_
  refine wp_strx (by decide) (by rw [o₆.get .x9, m₅.gpr, o₄.get .x9, m₃.gpr, x9]; rfl)
    (w _ (by rw [o₆.wr, m₅.wr, o₄.wr, m₃.wr, o₂.wr, o₁.wr]) 112 (by decide)) fun u₇ m₇ => ?_
  refine wp_strx (by decide) (by rw [m₇.gpr, o₆.get .x9, m₅.gpr, o₄.get .x9, m₃.gpr, x9]; rfl)
    (w _ (by rw [m₇.wr, o₆.wr, m₅.wr, o₄.wr, m₃.wr, o₂.wr, o₁.wr]) 120 (by decide)) fun u₈ m₈ => ?_
  refine wp_strx (by decide) (by rw [m₈.gpr, m₇.gpr, o₆.get .x9, m₅.gpr, o₄.get .x9, m₃.gpr, x9]; rfl)
    (w _ (by rw [m₈.wr, m₇.wr, o₆.wr, m₅.wr, o₄.wr, m₃.wr, o₂.wr, o₁.wr]) 128 (by decide)) fun u₉ m₉ => wp_nil ?_
  refine ⟨(o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (o₄.keep.trans (m₅.keep.trans (o₆.keep.trans
    (m₇.keep.trans (m₈.keep.trans m₉.keep)))))))).mono, ?_⟩
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → u₈.gpr r = a.gpr r := fun r h9 h10 => by
    rw [m₈.gpr, m₇.gpr, o₆.get r (by simpa using h10), m₅.gpr, o₄.get r (by simpa using h10), m₃.gpr,
      o₂.get r (by simpa using h10), o₁.get r (by simpa using h9)]
  have h25 : u₈.gpr .x25 = a.gpr .x25 := g _ (by decide) (by decide)
  have h24 : u₇.gpr .x24 = a.gpr .x24 := by rw [← m₈.gpr]; exact g _ (by decide) (by decide)
  have ha : u₆.gpr .x10 = BitVec.ofNat 64 H.D := by rw [e₆, setWidth_ofNat16 hD]
  have hb : u₄.gpr .x10 = a.gpr .x24 + a.gpr .x25 := by
    rw [e₄, m₃.gpr, o₂.get .x24, o₂.get .x25, o₁.get .x24, o₁.get .x25]
  have hc : u₂.gpr .x10 = a.gpr .x20 + BitVec.ofNat 64 mgfOff := by rw [e₂, o₁.get .x20]
  rw [m₉.mem, m₈.mem, m₇.mem, o₆.mem, m₅.mem, o₄.mem, m₃.mem, o₂.mem, o₁.mem, h25, h24, ha, hb, hc]
  rfl

theorem mF_off (F : Addr) (d : Nat) : off (mF F) (mgfFrame + d) = off F d := by
  simp only [mF, off, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The words MGF1's slots and the arguments' block write are in its frame. -/
theorem argsMem_frame (a : State) (F' : Addr) (D : Nat) : Frame [⟨F', 272⟩] a.mem (argsMem a F' D) := by
  have c : ∀ d, d + 8 ≤ 272 → (⟨F', 272⟩ : Region).Contains (off F' d) (64 / 8) := fun d hd =>
    Offset.contains_base F' hd (by omega)
  exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 96 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 104 (by decide))).writeW (List.mem_singleton_self _) _ (c 112 (by decide))).writeW
    (List.mem_singleton_self _) _ (c 120 (by decide))).writeW (List.mem_singleton_self _) _ (c 128 (by decide)))

/-- `x` in `[p, p + 8192)` is `p + o` for some `o < 8192`. -/
theorem of_contains {p x : Addr} (h : (⟨p, 8192⟩ : Region).Contains x 1) :
    ∃ o < 8192, x = off p o :=
  ⟨(x - p).toNat, by simp only [Region.Contains] at h; omega,
    by rw [off, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]⟩

/-- OAEP's view of the words of MGF1's frame after the arguments' block. -/
def argsW (a : State) (F' : Addr) (D : Nat) : Nat → BitVec 64 :=
  Proof.RsaOaep.AArch64.upd (Proof.RsaOaep.AArch64.upd (Proof.RsaOaep.AArch64.upd (Proof.RsaOaep.AArch64.upd
    (Proof.RsaOaep.AArch64.upd (fun k => Proof.RsaOaep.AArch64.word a.mem F' (8 * k)) 12
      (a.gpr .x20 + BitVec.ofNat 64 mgfOff)) 13 (a.gpr .x24 + a.gpr .x25)) 14 (BitVec.ofNat 64 D)) 15
    (a.gpr .x24)) 16 (a.gpr .x25)

theorem args_rep {a : State} {F' S' : Addr} {D : Nat} (Ge : Proof.RsaOaep.AArch64.Geo F' S') :
    Proof.RsaOaep.AArch64.Rep (argsMem a F' D) F' S' (fun o => a.mem (off S' o)) (argsW a F' D) :=
  let R0 : Proof.RsaOaep.AArch64.Rep a.mem F' S' (fun o => a.mem (off S' o))
      (fun k => Proof.RsaOaep.AArch64.word a.mem F' (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  ((((R0.wf Ge (k := 12) (by decide) _).wf Ge (k := 13) (by decide) _).wf Ge (k := 14) (by decide) _).wf Ge
    (k := 15) (by decide) _).wf Ge (k := 16) (by decide) _

section
variable {G : Impl.Pbkdf2.Md.AArch64.Stream} (hG : VG.Proof.Pbkdf2.Md.AArch64.Calls.StreamOK G)

/-- MGF1's arguments to its slots, in its frame: OAEP's MGF1 then runs from
the state reached, as OAEP's proofs need. -/
theorem setup_ok {H : Hash} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {t : State} {F S p : Addr}
    (L : Lay t F S) {e db : Nat} (hd : DbAt H.D e db)
    (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db) (E : Env G g t F S p) :
    WP isa (.block (mgfArgs H)) (allocated mgfFrame t) fun u => Keep [.x9, .x10] (allocated mgfFrame t) u ∧
      u.syms = t.syms ∧ u.mem = argsMem t (mF F) H.D ∧ Proof.RsaOaep.AArch64.Lay u (mF F) (off S mgfOff) ∧
      Proof.RsaOaep.AArch64.Rep u.mem (mF F) (off S mgfOff) (fun o => t.mem (off (off S mgfOff) o))
        (argsW t (mF F) H.D) ∧
      Proof.RsaOaep.AArch64.Table.Tab G g (mF F) (off S mgfOff) p (mgfFrame + sMgfT) u ∧
      Proof.RsaOaep.AArch64.MFit (e + db - mgfOff) H.D (e - mgfOff) db ∧
      Proof.RsaOaep.AArch64.MArgs (argsW t (mF F) H.D) (off S mgfOff) (e + db - mgfOff) H.D (e - mgfOff) db := by
  have hfit := hd.fit
  have he1 := hd.e1
  have hdb1 := hd.db1
  have c1 : oY = 3584 := rfl
  have c7 : oEm = 2560 := rfl
  have hF := E.F288
  have Ge := E.geo
  have asp : (allocated mgfFrame t).sp = mF F := by simp [allocated, L.sp, mF]
  refine WP.mono_syms (args_ok H (by omega) asp fun d hd' => ⟨_, List.mem_cons_self, by
    rw [L.sp, mgfFrame_eq]; exact Offset.contains_base _ hd' (by omega)⟩) fun u ⟨K, hm⟩ syu => ?_
  have hsu : u.sp = mF F := by rw [K.sp, asp]
  have hwu : u.wr = ⟨mF F, 272⟩ :: t.wr := by rw [K.wr]; simp [allocated, L.sp, mF, mgfFrame_eq]
  have hru : u.rd = t.rd := by rw [K.rd]; rfl
  have hsy : u.syms = t.syms := syu
  have hum : u.mem = argsMem t (mF F) H.D := hm
  have R5 : Proof.RsaOaep.AArch64.Rep u.mem (mF F) (off S mgfOff) (fun o => t.mem (off (off S mgfOff) o))
      (argsW t (mF F) H.D) := by rw [hum]; exact args_rep Ge
  have w : ∀ k, k < 12 ∨ 16 < k → argsW t (mF F) H.D k = Proof.RsaOaep.AArch64.word t.mem (mF F) (8 * k) := by
    intro k hk
    have : k ≠ 12 ∧ k ≠ 13 ∧ k ≠ 14 ∧ k ≠ 15 ∧ k ≠ 16 := by omega
    simp [argsW, Proof.RsaOaep.AArch64.upd, this]
  have hsc : Covers [⟨off S mgfOff, 8192⟩] u.wr := fun a n h => by
    obtain ⟨r, hr, hc⟩ := E.sc a n h; exact ⟨r, by rw [hwu]; exact List.mem_cons_of_mem _ hr, hc⟩
  have L' : Proof.RsaOaep.AArch64.Lay u (mF F) (off S mgfOff) :=
    ⟨hsu, fun a n ⟨r, hr, hc⟩ => ⟨⟨mF F, 272⟩, by rw [hwu]; exact List.mem_cons_self, by
      rw [List.mem_singleton.mp hr] at hc; exact hc⟩, hsc,
      by rw [show Impl.RsaOaep.AArch64.sScr = 8 * 12 from rfl, R5.fr 12 (by decide)]
         simp [argsW, Proof.RsaOaep.AArch64.upd, L.x20], Ge⟩
  have fr0 : Frame [⟨mF F, 272⟩] t.mem u.mem := by rw [hum]; exact argsMem_frame t (mF F) H.D
  have hArg : off (mF F) (mgfFrame + sMgfT) = off F sMgfT := mF_off F sMgfT
  have T : Proof.RsaOaep.AArch64.Table.Tab G g (mF F) (off S mgfOff) p (mgfFrame + sMgfT) u := {
    ok := by rw [hsy]; exact E.ok
    rd := fun j hj => by rw [hru, hwu, InRegions_append_cons]; exact .inr (E.rd j hj)
    rdD := by rw [hru, hwu, InRegions_append_cons]; exact .inr E.rdD
    rdA := by
      rw [hru, hwu, InRegions_append_cons, show Proof.RsaOaep.AArch64.off (mF F) (mgfFrame + sMgfT) = off F sMgfT
        from hArg]
      exact .inr (L.fld (by decide))
    mem := fun m hf => by
      have Fm : Frame [below F (mgfFrame + 16), ⟨off S mgfOff, 8192⟩] t.mem m :=
        (((fr0.mono (by simp [Proof.RsaOaep.AArch64.Table.mgfRs]; left; rfl)).trans hf)).sub fun r hr => by
          simp only [Proof.RsaOaep.AArch64.Table.mgfRs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ⟨_, List.mem_cons_self, sub_mF F⟩
          · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
          · exact ⟨_, List.mem_cons_self, sub_retR F⟩
      obtain ⟨tm, hdl⟩ := E.mem m (Fm.mono (by simp [mgfWr]))
      refine ⟨by rw [hsy]; exact tm, hdl, ?_⟩
      rw [show Proof.RsaOaep.AArch64.off (mF F) (mgfFrame + sMgfT) = off F sMgfT from hArg,
        Fm.readW (r := slotR F sMgfT) (Region.contains_self _ _) (fun r hr => ?_) (by decide), E.slot]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_below F (n := 288) (d := sMgfT) (k := 8) (by have := F.isLt; unfold sMgfT; omega)
      · exact E.dFw.sub_left (Offset.sub_base F (d := sMgfT) (n := 8) (by decide)) }
  have hMF : Proof.RsaOaep.AArch64.MFit (e + db - mgfOff) H.D (e - mgfOff) db :=
    ⟨by unfold Impl.RsaOaep.AArch64.oSt mgfOff; omega, by unfold Impl.RsaOaep.AArch64.oSt mgfOff; omega,
      .inr (by unfold mgfOff; omega), hdb1, by omega⟩
  have so : ∀ d, mgfOff ≤ d → off S d = off (off S mgfOff) (d - mgfOff) := fun d hd' => by
    rw [off_off, Nat.add_sub_cancel' hd']
  have hMA : Proof.RsaOaep.AArch64.MArgs (argsW t (mF F) H.D) (off S mgfOff) (e + db - mgfOff) H.D (e - mgfOff) db :=
    ⟨by show t.gpr .x24 + t.gpr .x25 = _; rw [h24, h25, off_add, so _ (by unfold mgfOff; omega)],
      by show BitVec.ofNat 64 H.D = _; rfl,
      by show t.gpr .x24 = _; rw [h24, so _ (by unfold mgfOff; omega)],
      by show t.gpr .x25 = _; rw [h25]⟩
  exact ⟨K, hsy, hum, L', R5, T, hMF, hMA⟩

include hG in
/-- `DB ⊕= MGF1(H, dbLen)` for `H` the `hLen` bytes after `DB`, with MGF1's
hash function `G`, that of the table whose address is in the slot
`sMgfT`. -/
theorem mgfXor_ok {H : Hash} {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
    (hGv : Proof.Mgf1.Valid Gs) {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {t : State} {F S p : Addr}
    (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {e db : Nat} (hd : DbAt H.D e db)
    (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db) (E : Env G g t F S p) :
    WP isa (mgfXor H g) t fun t' => t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) ∧
      (∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) ∧
      Frame (mgfWr F S) t.mem t'.mem ∧ t'.syms = t.syms ∧
      ∀ o, oEm ≤ o → o < oY →
        t'.mem (off S o) = mixV V (Spec.Mgf1.mgf1 Gs ((List.range H.D).map fun i => V (e + db + i)) db) e db o := by
  have hfit := hd.fit
  have he1 := hd.e1
  have hdb1 := hd.db1
  have c1 : oY = 3584 := rfl
  have c7 : oEm = 2560 := rfl
  have hF := E.F288
  unfold mgfXor
  refine WP.alloc (by decide) (by rw [L.sp, mgfFrame_eq]; rw [mgfFrame_eq] at hF; omega) ?_
  refine WP.seq ?_
  have asp : (allocated mgfFrame t).sp = mF F := by simp [allocated, L.sp, mF]
  refine WP.mono (setup_ok L hd h24 h25 E) fun u ⟨K, hsy, hum, L', R5, T, hMF, hMA⟩ => ?_
  have hsu : u.sp = mF F := by rw [K.sp, asp]
  have hwu : u.wr = ⟨mF F, 272⟩ :: t.wr := by rw [K.wr]; simp [allocated, L.sp, mF, mgfFrame_eq]
  have hru : u.rd = t.rd := by rw [K.rd]; rfl
  have fr0 : Frame [⟨mF F, 272⟩] t.mem u.mem := by rw [hum]; exact argsMem_frame t (mF F) H.D
  have so : ∀ d, mgfOff ≤ d → off S d = off (off S mgfOff) (d - mgfOff) := fun d hd' => by
    rw [off_off, Nat.add_sub_cancel' hd']
  refine WP.mono_syms (Proof.RsaOaep.AArch64.Table.mgfXorT_ok hG hGh hGl hGv (sArg := mgfFrame + sMgfT) (by decide)
    T L' R5 hMF hMA) fun u' ⟨_, st, V', W', R', _, hV'⟩ sy' => ?_
  have hsp' : u'.sp = mF F := st.sp.trans hsu
  have hcs : ∀ r ∈ preserved, r ≠ .x30 → u'.gpr r = t.gpr r := fun r hr h30 => by
    rw [st.cs r hr h30, K.gpr r (by revert r; decide)]; rfl
  have hfr : Frame (mgfWr F S) t.mem u'.mem := by
    intro x hx
    have hx1 : ¬ (⟨S, oRsa⟩ : Region).Contains x 1 := hx _ (by simp [mgfWr])
    have hx2 : ¬ (below F (mgfFrame + 16)).Contains x 1 := hx _ (by simp [mgfWr])
    by_cases hc : (⟨off S mgfOff, 8192⟩ : Region).Contains x 1
    · obtain ⟨o, ho, rfl⟩ := of_contains hc
      have ho' : 7680 ≤ o := by
        refine Nat.le_of_not_lt fun hlt => hx1 ?_
        rw [off_off]
        exact Offset.contains_base S (d := mgfOff + o) (n := 1) (by unfold mgfOff oRsa; omega) (by unfold mgfOff; omega)
      have hmo : Proof.RsaOaep.AArch64.mOut o := (Proof.RsaOaep.AArch64.mOut_iff o).mpr
        (.inr (.inr (.inr (by unfold Impl.RsaOaep.AArch64.oW; omega))))
      refine (R'.scr o (by unfold Impl.RsaOaep.AArch64.oRsa; omega)).trans ((hV' o (by unfold Impl.RsaOaep.AArch64.oRsa; omega) hmo).trans ?_)
      simp only [Proof.RsaOaep.mixV]
      rw [ite_eq_right (by unfold mgfOff; omega)]
    · have h₁ : ¬ (⟨mF F, 272⟩ : Region).Contains x 1 := fun h => hx2 (sub_mF F x h)
      rw [st.frame x fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h₁
          · exact hc
          · exact fun h => hx2 (sub_retR F x h),
        fr0 x fun r hr => by rw [List.mem_singleton.mp hr]; exact h₁]
  refine ⟨?_, by show u'.rd = t.rd; rw [st.rd, hru], by show u'.wr.tail = t.wr; rw [st.wr, hwu]; rfl, hcs,
    fun r hr => (st.vec r hr).trans (K.vcs r hr), hfr, by rw [show (freed mgfFrame u').syms = u'.syms from rfl, sy', hsy],
    fun o ho₁ ho₂ => ?_⟩
  · show u'.sp + BitVec.ofNat 64 mgfFrame = t.sp
    rw [hsp', L.sp, mF, BitVec.sub_add_cancel]
  · show u'.mem (off S o) = _
    have ho : o - mgfOff < 3072 := by unfold mgfOff; omega
    rw [so o (by unfold mgfOff; omega)]
    refine (R'.scr (o - mgfOff) (by unfold Impl.RsaOaep.AArch64.oRsa; omega)).trans
      ((hV' _ (by unfold Impl.RsaOaep.AArch64.oRsa; omega) ((Proof.RsaOaep.AArch64.mOut_iff _).mpr (.inl ho))).trans ?_)
    have hv : ∀ q, mgfOff ≤ q → q < oRsa → t.mem (off (off S mgfOff) (q - mgfOff)) = V q := fun q h₁ h₂ => by
      rw [← so q h₁]; exact R q h₂
    have hsrc : Proof.RsaOaep.srcB (fun o => t.mem (off (off S mgfOff) o)) (e + db - mgfOff) H.D =
        (List.range H.D).map fun i => V (e + db + i) := by
      simp only [Proof.RsaOaep.srcB]
      refine List.map_congr_left fun i hi => ?_
      have := List.mem_range.mp hi
      rw [show e + db - mgfOff + i = e + db + i - mgfOff by unfold mgfOff; omega]
      exact hv _ (by unfold mgfOff; omega) (by unfold oRsa; omega)
    simp only [Proof.RsaOaep.mixV, mixV, hsrc]
    rw [hv o (by unfold mgfOff; omega) (by unfold oRsa; omega)]
    by_cases hin : e ≤ o ∧ o < e + db
    · rw [ite_eq_left (by unfold mgfOff; omega), ite_eq_left hin, show o - mgfOff - (e - mgfOff) = o - e by unfold mgfOff; omega]
    · rw [ite_eq_right (by unfold mgfOff; omega), ite_eq_right hin]

end

/-! ## The tables at the entry -/

/-- What the code needs of the tables at `pH` (of `MdHash`) and `pG` (of
`Hash`) in the entry state `s`: the table of `MdHash` holds the addresses
of `H`'s `init`, compression function and digest (`dn`), which the calls of
`f` reach, and the table of `Hash` those of `G`'s functions, which the
calls of `g` reach, and `G`'s digest length. -/
structure TabsAt (H : Hash) (dn : String) (f : MdFns) (G : Impl.Pbkdf2.Md.AArch64.Stream)
    (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) (pH pG : Addr) (s : State) : Prop where
  h0 : s.mem.readW pH 64 = s.syms H.initN
  h3 : s.mem.readW (pH + BitVec.ofNat 64 24) 64 = s.syms H.compN
  h4 : s.mem.readW (pH + BitVec.ofNat 64 32) 64 = s.syms dn
  fi : Finds f.init s.syms (s.syms H.initN) H.initN H.initC
  fc : Finds f.comp s.syms (s.syms H.compN) H.compN H.compC
  fd : Finds f.dig s.syms (s.syms dn) dn (Impl.MdHashTable.AArch64.digest H.P)
  gok : Proof.RsaOaep.AArch64.Table.TabOK G g s.syms
  gm : Proof.RsaOaep.AArch64.Table.TabMem G s.syms pG s.mem
  gD : s.mem.readW (off pG 32) 64 = BitVec.ofNat 64 G.D

/-- A word of the table of `Hash`, after writes apart from it. -/
theorem tabG_keep {pG : Addr} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨pG, 40⟩ r) {d : Nat} (hd8 : d + 8 ≤ 40) :
    m'.readW (off pG d) 64 = m.readW (off pG d) 64 :=
  hf.readW (r := ⟨pG, 40⟩) (Offset.contains_base _ hd8 (by omega)) hd (by decide)

/-- The table of `Hash`, after writes apart from it. -/
theorem TabMem.keep {G : Impl.Pbkdf2.Md.AArch64.Stream} {sy : String → Addr} {pG : Addr} {rs : List Region}
    {m m' : Mem} (h : Proof.RsaOaep.AArch64.Table.TabMem G sy pG m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨pG, 40⟩ r) : Proof.RsaOaep.AArch64.Table.TabMem G sy pG m' :=
  ⟨(tabG_keep hf hd (d := 8 * 0) (by decide)).trans h.1, (tabG_keep hf hd (d := 8 * 1) (by decide)).trans h.2.1,
    (tabG_keep hf hd (d := 8 * 2) (by decide)).trans h.2.2⟩

end VG.Proof.RsaPss.AArch64
