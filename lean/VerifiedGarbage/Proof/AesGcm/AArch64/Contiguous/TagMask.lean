module

-- separate module: The AES round proof can be checked independently of the polynomial arithmetic in TagLengths.

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Tag
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
import VerifiedGarbage.Proof.Framework.Range

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Tag
open VG VG.AArch64
open VG.Impl.AesGcm.AArch64.Contiguous.Tag
open VG.Proof.Aes.AArch64.Aese
open VG.Proof.Gcm.AArch64.Stitch (sch)
open VG.Spec.Aes (roundKey addRoundKey)

abbrev changed : List VReg := [.v28,.v29]

private theorem setVec (s : State) {r : VReg} (h : r ∈ changed) (v : BitVec 128) :
    VFrame changed s (s.setV r v) :=
  ⟨rfl,rfl,rfl,rfl,rfl,fun _ hb => setV_v_of_ne _ _ (fun e => hb (e ▸ h))⟩

abbrev keyReadable (nr : Nat) (s : State) :=
  ∀ j ≤ nr, InRegions (s.rd ++ s.wr) (s.gpr .x21 + BitVec.ofNat 64 (16*j)) 16

abbrev invariant (w : List Byte) (x : Spec.Aes.State) (j : Nat) (s : State) :=
  addRoundKey (st (s.v .v28)) (roundKey w j) = rnds w x j

private theorem round_ok {nr j : Nat} (hn : nr ≤ 14) (hj : j < nr) {a s : State}
    (k : keyReadable nr a) (f : VFrame changed a s)
    {x : Spec.Aes.State} (v : invariant (sch nr a) x j s) :
    WP isa (.block (round j)) s fun t => invariant (sch nr a) x (j+1) t ∧ VFrame changed a t := by
  have rd : InRegions (s.rd ++ s.wr) (s.gpr .x21 + BitVec.ofNat 64 (16*j)) 16 := by
    rw [f.rd,f.wr,f.gpr]; exact k j (by omega)
  let key := s.mem.readW (s.gpr .x21 + BitVec.ofNat 64 (16*j)) 128
  have hk : KeyIs key (roundKey (sch nr a) j) := by
    dsimp [key]; rw [f.mem,f.gpr]; exact keyIs_readW _ _ (by omega)
  rw [round,WP.block_cons_iff]
  refine ⟨_, VG.Proof.Aes.AArch64.Aese.exec_ldrq (by omega) rd, ?_⟩
  let u := s.setV .v29 key
  refine WP.of_runBlock ⟨_,rnd_run .v29 .v28 u,?_,?_⟩
  · simpa [invariant,u,setV_v_self,setV_v_of_ne] using round_st hk v
  · exact (f.trans (setVec s (r := .v29) (by decide) key)).trans (setVec u (r := .v28) (by decide) _)

theorem rounds_ok {nr : Nat} (hn : nr ≤ 14) {s : State} (k : keyReadable nr s)
    (x : Spec.Aes.State) (h : invariant (sch nr s) x 0 s) :
    WP isa (.block ((List.range (nr-1)).flatMap round)) s fun t =>
      invariant (sch nr s) x (nr-1) t ∧ VFrame changed s t :=
  wp_range_flatMap (M := isa) (fun j t => invariant (sch nr s) x j t ∧ VFrame changed s t)
    (fun j _ hj ⟨v,f⟩ => round_ok hn (by omega) k f v) (nr-1) (Nat.le_refl _) s ⟨h,VFrame.refl _ _⟩

private theorem key_ok {nr j : Nat} (hn : nr ≤ 14) (hj : j ≤ nr) {a s : State}
    (k : keyReadable nr a) (f : VFrame changed a s) :
    WP isa (.block [.ldrq .v29 .x21 (16*j)]) s fun t =>
      KeyIs (t.v .v29) (roundKey (sch nr a) j) ∧ t.v .v28 = s.v .v28 ∧ VFrame changed a t := by
  have rd : InRegions (s.rd ++ s.wr) (s.gpr .x21 + BitVec.ofNat 64 (16*j)) 16 := by
    rw [f.rd,f.wr,f.gpr]; exact k j hj
  rw [WP.block_cons_iff]
  refine ⟨_,exec_ldrq (by omega) rd,WP.block_nil ⟨?_,setV_v_of_ne _ _ (by decide),f.trans (setVec s (by decide) _)⟩⟩
  rw [setV_v_self,f.mem,f.gpr]
  exact keyIs_readW _ _ (by omega)

private theorem last_ok {nr : Nat} (hn : nr ≤ 14) {a s : State} (k : keyReadable nr a)
    (f : VFrame changed a s) {x : Spec.Aes.State} (v : invariant (sch nr a) x (nr-1) s) :
    WP isa (.block (last nr)) s fun t => st (t.v .v28) = Spec.Aes.cipher nr (sch nr a) x ∧
      VFrame changed a t := by
  change WP isa (.block ([_] ++ [_] ++ ([_] ++ [_]))) s _
  rw [List.append_assoc,WP.block_append_iff]
  refine (key_ok hn (Nat.sub_le nr 1) k f).mono ?_
  intro u ⟨k1,u28,fu⟩
  rw [WP.block_append_iff]
  let r := aesMapBytes aesSbox (aesShiftRows (u.v .v28 ^^^ u.v .v29))
  refine WP.of_runBlock ⟨_,(rfl : runBlock isa [.vop (.aese .v28 .v29)] u = some (u.setV .v28 r)),?_⟩
  rw [WP.block_append_iff]
  refine (key_ok hn (Nat.le_refl nr) k (fu.trans (setVec u (by decide) r))).mono ?_
  intro w ⟨k2,w28,fw⟩
  refine WP.of_runBlock ⟨_,(rfl : runBlock isa [.vop (.logic .eor .v28 .v28 .v29)] w =
    some (w.setV .v28 (w.v .v28 ^^^ w.v .v29))),?_,fw.trans (setVec w (by decide) _)⟩
  rw [setV_v_self,w28,setV_v_self]
  exact last_st k1 k2 (by simpa only [u28] using v : addRoundKey (st (u.v .v28)) _ = _)

theorem mask_ok {nr : Nat} (hn : nr ≤ 14) (s : State) (k : keyReadable nr s)
    (rd : InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 0) 16) :
    WP isa (.block (mask nr)) s fun t =>
      st (t.v .v28) = Spec.Aes.cipher nr (sch nr s) (st (s.mem.readW (s.gpr .x20) 128)) ∧
      VFrame changed s t := by
  let block := s.mem.readW (s.gpr .x20) 128
  let u := s.setV .v28 block
  have run : exec (.ldrq .v28 .x20 0) s = some u := by
    simpa only [BitVec.add_zero] using (exec_ldrq (s := s) (t := .v28) (n := .x20) (off := 0) (by decide) rd)
  have fu : VFrame changed s u := setVec s (r := .v28) (by decide) block
  have ku : keyReadable nr u := k
  have start : invariant (sch nr s) (st block) 0 u := by
    change addRoundKey (st ((s.setV .v28 block).v .v28)) _ = _
    rw [setV_v_self,rnds_zero]
  rw [mask,List.append_assoc,List.singleton_append,WP.block_cons_iff]
  refine ⟨u,run,?_⟩
  rw [WP.block_append_iff]
  refine (rounds_ok (s := u) hn ku (st block) start).mono ?_
  intro z ⟨v,f⟩
  exact last_ok hn k (fu.trans f) v

end VG.Proof.AesGcm.AArch64.Contiguous.Tag
