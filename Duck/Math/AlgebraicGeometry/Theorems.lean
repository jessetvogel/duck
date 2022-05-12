import Duck.Math.AlgebraicGeometry.Scheme

namespace Math.AlgebraicGeometry

open SchemeHom

section theorems

variable {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z}

@[aesop 99%] axiom qc_of_af (h : X.affine) : X.quasi_compact
@[aesop 99%] axiom lnt_of_rg (h : X.regular) : X.locally_noetherian
@[aesop 99%] axiom nt_of_lnt_qc (h1 : X.locally_noetherian) (h2 : X.quasi_compact) : X.noetherian
@[aesop 99%] axiom lnt_of_nt (h1 : X.noetherian) : X.locally_noetherian
@[aesop 99%] axiom qc_of_nt (h1 : X.noetherian) : X.quasi_compact
@[aesop 99%] axiom rd_of_int (h : X.integral) : X.reduced
@[aesop 99%] axiom irr_of_int (h : X.integral) : X.irreducible
@[aesop 99%] axiom int_of_rd_irr (h1 : X.reduced) (h2 : X.irreducible) : X.integral
@[aesop 99%] axiom cm_of_rg (h : X.regular) : X.cohen_macaulay
@[aesop 99%] axiom cn_of_int (h : X.integral) : X.connected
@[aesop 99%] axiom rd_of_rg (h : X.regular) : X.reduced
@[aesop 99%] axiom sp_of_af (h : X.affine) : X.separated
@[aesop 99%] axiom qsp_of_sp (h : X.separated) : X.quasi_separated
@[aesop 99%] axiom qsp_of_lnt (h : X.locally_noetherian) : X.quasi_separated
@[aesop 99%] axiom cn_of_irr (h : X.irreducible) : X.connected
@[aesop 99%] axiom lnt_of_cm (h : X.cohen_macaulay) : X.locally_noetherian
@[aesop 99%] axiom nm_of_rg (h : X.regular) : X.normal

end theorems

section theorems

variable {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z}

@[aesop 99%] axiom sm_of_fsm_lfp { X Y : Scheme} {f : X ⟶ Y} (h1 : formally_smooth f) (h2 : locally_finitely_presented f) : smooth f
@[aesop 99%] axiom fsm_of_sm (h : smooth f) : formally_smooth f
@[aesop 99%] axiom lfp_of_sm (h : smooth f) : locally_finitely_presented f
@[aesop 99%] axiom et_of_fet_lfp (h1 : formally_etale f) (h2 : locally_finitely_presented f) : etale f
@[aesop 99%] axiom fet_of_et (h : etale f) : formally_etale f
@[aesop 99%] axiom lfp_of_et (h : etale f) : locally_finitely_presented f
@[aesop 99%] axiom ur_of_fur_lft (h1 : formally_unramified f) (h2 : locally_finite_type f) : unramified f
@[aesop 99%] axiom fur_of_ur (h : unramified f) : formally_unramified f
@[aesop 99%] axiom lft_of_ur (h : unramified f) : locally_finite_type f
@[aesop 99%] axiom fsm_of_fet (h : formally_etale f) : formally_smooth f
@[aesop 99%] axiom fur_of_fet (h : formally_etale f) : formally_unramified f
@[aesop 99%] axiom fet_of_fsm_fur (h1 : formally_smooth f) (h2 : formally_unramified f) : formally_etale f
@[aesop 99%] axiom fp_of_lfp_qsp_qc (h1 : locally_finitely_presented f) (h2 : quasi_separated f) (h3 : quasi_compact f) : finitely_presented f
@[aesop 99%] axiom lfp_of_fp (h : finitely_presented f) : locally_finitely_presented f
@[aesop 99%] axiom qsp_of_fp (h : finitely_presented f) : quasi_separated f
@[aesop 99%] axiom qc_of_fp (h : finitely_presented f) : quasi_compact f
@[aesop 99%] axiom lft_of_lfp (h : locally_finitely_presented f) : locally_finite_type f
@[aesop 99%] axiom ft_of_fp (h : finitely_presented f) : finite_type f
@[aesop 99%] axiom ft_of_lft_qc (h1 : locally_finite_type f) (h2 : quasi_compact f) : finite_type f
@[aesop 99%] axiom lft_of_ft (h : finite_type f) : locally_finite_type f
@[aesop 99%] axiom qc_of_ft (h : finite_type f) : quasi_compact f
@[aesop 99%] axiom qc_of_af_morph (h : affine f) : quasi_compact f
@[aesop 99%] axiom af_of_fn (h : finite f) : affine f
@[aesop 99%] axiom pr_of_fn (h : finite f) : proper f
@[aesop 99%] axiom fn_of_af_pr (h1 : affine f) (h2 : proper f): finite f
@[aesop 99%] axiom op_of_fl_lfp (h1 : flat f) (h2 : locally_finitely_presented f) : open_morphism f
@[aesop 99%] axiom pr_of_ft_uc_sp (h1 : finite_type f) (h2: universally_closed f) (h3 : separated f) : proper f
@[aesop 99%] axiom ft_of_pr (h : proper f) : finite_type f
@[aesop 99%] axiom uc_of_pr (h : proper f) : universally_closed f
@[aesop 99%] axiom sp_of_pr (h : proper f) : separated f
@[aesop 99%] axiom lfp_of_lft_lnt (h1 : locally_finite_type f) (h2 : Y.locally_noetherian) : locally_finitely_presented f
@[aesop 99%] axiom qc_of_uc (h : universally_closed f) : quasi_compact f
@[aesop 99%] axiom pr_of_ci (h : closed_immersion f) : proper f
@[aesop 99%] axiom qsp_of_lft_lnt (h1 : locally_finite_type f) (h2 : Y.locally_noetherian) : quasi_separated f
@[aesop 99%] axiom ft_of_ci (h : closed_immersion f) : finite_type f
@[aesop 99%] axiom qc_of_im_lnt (h1 : immersion f) (h2 : Y.locally_noetherian) : quasi_compact f
@[aesop 99%] axiom qc_of_src_nt {X Y : Scheme} (f : X ⟶ Y) (h : X.noetherian) : quasi_compact f
@[aesop 99%] axiom qsp_of_sp_morph (h : separated f) : quasi_separated f
@[aesop 99%] axiom qc_of_qfn (h : quasi_finite f) : quasi_compact f
@[aesop 99%] axiom ff_of_qf (h : quasi_finite f) : finite_fibers f
@[aesop 99%] axiom qfn_of_qc_ff (h1 : quasi_compact f) (h2 : finite_fibers f) : quasi_finite f
@[aesop 99%] axiom et_of_oi (h : open_immersion f) : etale f
@[aesop 99%] axiom sp_of_oi (h : open_immersion f) : separated f
@[aesop 99%] axiom ffl_of_fl_sj (h1 : flat f) (h2 : surjective f) : faithfully_flat f
@[aesop 99%] axiom fl_of_ffl (h : faithfully_flat f) : flat f
@[aesop 99%] axiom sj_of_ffl (h : faithfully_flat f) : surjective f
@[aesop 99%] axiom sp_of_af_morph (h : affine f) : separated f
@[aesop 99%] axiom qfn_of_fn (h : finite f) : quasi_finite f
@[aesop 99%] axiom fl_of_sm (h : smooth f) : flat f
def ur_of_et (h : etale f) := ur_of_fur_lft (fur_of_fet (fet_of_et h)) (lft_of_lfp (lfp_of_et h))
def sm_of_et (h : etale f) := sm_of_fsm_lfp (fsm_of_fet (fet_of_et h)) (lfp_of_et h)
@[aesop 99%] axiom qf_of_oi (h : open_immersion f) : quasi_finite f
@[aesop 99%] axiom fn_of_pr_qf (h1 : proper f) (h2 : quasi_finite f) : finite f
@[aesop 99%] axiom op_of_fl_lft (h1 : flat f) (h2 : locally_finite_type f) : open_morphism f
@[aesop 99%] axiom syn_of_fl_lci (h1 : flat f) (h2 : lci f) : syntomic f
@[aesop 99%] axiom fl_of_syn (h : syntomic f) : flat f
@[aesop 99%] axiom lci_of_syn (h : syntomic f) : lci f

@[aesop 99%] axiom src_af_of_af_trg_af (h1: Y.affine) (h2 : affine f) : X.affine
@[aesop 99%] axiom af_of_src_af_trg_af {X Y : Scheme} (f : X ⟶ Y) (h1 : X.affine) (h2: Y.affine) : affine f
@[aesop 99%] axiom src_qc_of_qc_trg_qc (h1 : Y.quasi_compact) (h2 : quasi_compact f) : X.quasi_compact
@[aesop 99%] axiom src_rg_of_sm_trg_rg (h1 : Y.regular) (h2 : smooth f) : X.regular
@[aesop 99%] axiom src_jc_of_lft_trg_jc (h1 : Y.jacobson) (h2 : locally_finite_type f) : X.jacobson
@[aesop 99%] axiom sp_of_src_af (h : X.affine) : separated f 
@[aesop 99%] axiom trg_sp_of_uc_sj_src_sp (h1 : X.separated) (h2 : universally_closed f) (h3 : surjective f) : Y.separated
@[aesop 99%] axiom trg_qsp_of_uc_sj_src_qsp (h1 : X.quasi_separated) (h2 : universally_closed f) (h3 : surjective f) : Y.quasi_separated
@[aesop 99%] axiom comp_qsep_left_univcl_surj_imp_right_qsep (h1 : universally_closed f) (h2 : surjective f) (h3 : quasi_separated (g ≫ f)) : quasi_separated g
@[aesop 99%] axiom comp_sep_left_univcl_surj_imp_right_qsep (h1 : universally_closed f) (h2 : surjective f) (h3 : quasi_separated (g ≫ f)) : quasi_separated g

@[aesop 99%] axiom etc_of_zrc (h : zariski_cover f) : etale_cover f
@[aesop 99%] axiom smc_of_etc (h : etale_cover f) : smooth_cover f
@[aesop 99%] axiom syc_of_smc (h : smooth_cover f) : syntomic_cover f
@[aesop 99%] axiom fppf_of_syc (h : syntomic_cover f) : fppf_cover f
@[aesop 99%] axiom fpqc_of_fppf (h : fppf_cover f) : fpqc_cover f
@[aesop 99%] axiom sm_of_smc (h : smooth_cover f) : smooth f
@[aesop 99%] axiom sj_of_smc (h : smooth_cover f) : surjective f
@[aesop 99%] axiom smc_of_sm_sj (h1 : smooth f) (h2 : surjective f) : smooth_cover f
@[aesop 99%] axiom et_of_etc (h : etale_cover f) : etale f
@[aesop 99%] axiom sj_of_etc (h : etale_cover f) : surjective f
@[aesop 99%] axiom etc_of_et_sj (h1 : etale f) (h2 : surjective f) : etale_cover f 
@[aesop 99%] axiom syn_of_syc (h : syntomic_cover f) : syntomic f

@[aesop 99%] axiom fl_of_fppf (h : fppf_cover f) : flat f
@[aesop 99%] axiom sj_of_fppf (h : fppf_cover f) : surjective f
@[aesop 99%] axiom lfp_of_fppf (h : fppf_cover f) : locally_finitely_presented f
@[aesop 99%] axiom fppf_of_fl_sj_lfp (h1 : flat f) (h2 : surjective f) (h3 : locally_finitely_presented f) : fppf_cover f
@[aesop 99%] axiom zrc_of_iso (h : f.isomorphism) : zariski_cover f
@[aesop 99%] axiom zrc_of_sj_oi (h1 : surjective f) (h2 : open_immersion f) : zariski_cover f
@[aesop 99%] axiom fl_of_fpqc (h : fpqc_cover f) : flat f
@[aesop 99%] axiom sj_of_fpqc (h : fpqc_cover f) : surjective f

@[aesop 99%] axiom property_comp {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} {P : {T S : Scheme} → (h : T ⟶ S) → Prop} (hf : P f) (hg : P g) (hP : stable_composition P) : P (g ≫ f)
@[aesop 99%] axiom stable_comp_pr : stable_composition proper

end theorems

end Math.AlgebraicGeometry

