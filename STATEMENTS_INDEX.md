# Statements index

The statement library of this Lake project: `QUNets/Statements/*.lean` (statements only, each with `sorry`), the
roots `Challenge.lean` (statements) and `Solution.lean` (proofs), and one Comparator configuration, `comparator.json`,
with **616 compared theorems**. Paper: L. Gruenschloss, *Low-discrepancy quasi-uniform digital nets in every
dimension*, version 1 (`paper/core.tex`). Results are cited by their `\label`, never by number. The table maps every
compared theorem to the paper labels it formalizes; `scripts/gen_blueprint.py` reads it for the `\lean{}` links of the
blueprint. The Palomar headline entry (`Headline/`, `comparatorHeadline.json`, `palomar/headline/formalization.yaml`)
states `thm:A` in a Mathlib-only Challenge; its theorem `Z3NetA.theoremA` is the library theorem `Z3NetA.thmA`.

## Statement files

| file | paper | compared theorems |
|---|---|---|
| `QUNets/Statements/Prelim.lean` | sec:prelim | 19 |
| `QUNets/Statements/Frames.lean` | sec:frames | 50 |
| `QUNets/Statements/ThmA.lean` | sec:dims | 66 |
| `QUNets/Statements/Skeleton.lean` | sec:skel | 67 |
| `QUNets/Statements/Dim3.lean` | sec:dim3, sec:m3 | 67 |
| `QUNets/Statements/Base23.lean` | sec:base23 | 21 |
| `QUNets/Statements/DGS.lean` | sec:dgs | 64 |
| `QUNets/Statements/Deficit.lean` | sec:deficit, sec:deficitgrowth, sec:drift | 75 |
| `QUNets/Statements/WhyLat.lean` | sec:whylat | 14 |
| `QUNets/Statements/Large.lean` | sec:large (sec:S1E, sec:twocoset, sec:wnet) | 81 |
| `QUNets/Statements/Split.lean` | sec:large (split frames) | 78 |
| `QUNets/Statements/Appendix.lean` | app:perprime | 14 |
| **total** | | **616** |

## Per-theorem map

### `QUNets/Statements/Prelim.lean`

| Lean | paper |
|---|---|
| `Z3NetF.graphForm_of_box` | `sec:prelim` |
| `Z3NetF.nie_box` | `lem:nie` |
| `Z3NetF.nie_net` | `lem:nie` |
| `Z3NetF.nie_net_field` | `lem:nie` |
| `Z3NetF.nie_zmod` | `lem:nie` |
| `Z3NetF.box_minor` | `lem:box` |
| `Z3NetF.box_minor_self` | `lem:box` |
| `Z3NetF.gauge_diag` | `lem:box` |
| `Z3NetF.gauge_LU` | `lem:box` |
| `Z3NetF.gauge_scale3` | `lem:box` |
| `Z3NetF.gauge_net` | `lem:box` |
| `Z3NetF.gauge_net3` | `lem:box` |
| `Z3NetF.Ss_coord` | `lem:Ss` |
| `Z3NetF.Ss_sep` | `lem:Ss` |
| `Z3NetF.remK_bad` | `rem:K` |
| `Z3NetF.remK_good` | `rem:K` |
| `Z3NetF.digPointShift_eq_dshiftPt` | `def:dshift` |
| `Z3NetF.digPointShift_zero` | `def:dshift` |
| `Z3NetU.U_row0` | `lem:Ss` |

### `QUNets/Statements/Frames.lean`

| Lean | paper |
|---|---|
| `Z3NetF.wN_cauchy` | `sec:frames` |
| `Z3NetF.hermite_det` | `lem:hermite` |
| `Z3NetF.hermite_ne_zero` | `lem:hermite` |
| `Z3NetF.hermite_rows` | `lem:hermite` |
| `Z3NetF.frame_minor` | `lem:Ts` |
| `Z3NetF.frame_net_iff` | `lem:Ts` |
| `Z3NetF.frameGraph_spec` | `sec:frames`, `lem:Rs` |
| `Z3NetF.Rs_row0` | `lem:Rs` |
| `Z3NetF.Ns_row0` | `prop:Ns` |
| `Z3NetF.Gs_beta` | `prop:Gs` |
| `Z3NetF.Gs_gauge` | `prop:Gs` |
| `Z3NetF.Gs_row0` | `prop:Gs` |
| `Z3NetF.PGen_indep` | `prop:Gs`, `def:Ns` |
| `Z3NetF.tsk_unit` | `def:Ns`, `cor:tsk` |
| `Z3NetF.tsk_net` | `def:Ns`, `cor:tsk` |
| `Z3NetF.away_hom` | `def:Ns`, `cor:tsk` |
| `Z3NetF.projlines_frame` | `rem:projlines` |
| `Z3NetF.projlines` | `rem:projlines` |
| `Z3NetF.projlines_zmod` | `rem:projlines` |
| `Z3NetF.projlines_box` | `rem:projlines` |
| `Z3NetF.rowScale_box` | `rem:projlines` |
| `Z3NetF.rowScale_net` | `rem:projlines` |
| `Z3NetF.tsk_net_rowScale` | `rem:projlines`, `cor:tsk` |
| `Z3NetF.rowScale_rowRel` | `rem:projlines` |
| `Z3NetF.Ss_sep_rowScale` | `rem:projlines`, `lem:Ss`, `prop:k1` |
| `Z3NetF.D_sep_rowScale` | `rem:projlines`, `prop:D` |
| `Z3NetF.F_reach_iff` | `prop:F` |
| `Z3NetF.F_poly_iff` | `prop:F` |
| `Z3NetF.F_finite` | `prop:F` |
| `Z3NetF.CH_C` | `lem:CH` |
| `Z3NetF.CH_C_neg` | `lem:CH` |
| `Z3NetF.CH_C_classes` | `lem:CH` |
| `Z3NetF.CH_P` | `lem:CH` |
| `Z3NetF.CH_H` | `lem:CH` |
| `Z3NetF.CH_X` | `lem:CH` |
| `Z3Net.faure_Lam` | `prop:faure` |
| `Z3Net.faure_tau` | `prop:faure` |
| `Z3Net.faure_tau2` | `prop:faure` |
| `Z3Net.faure_DP` | `prop:faure` |
| `Z3Net.faure_reindex` | `prop:faure` |
| `Z3Net.projlines_P` | `rem:projlines`, `def:net` |
| `Z3Net.P_net_rowScale` | `rem:projlines`, `thm:t0` |
| `Z3Net.P_sep_rowScale` | `rem:projlines`, `thm:sep` |
| `Z3NetU.U_frameMinor` | `lem:Ts` |
| `Z3NetU.U_propN` | `prop:Ns` |
| `Z3NetU.U_propG` | `prop:Gs` |
| `Z3NetU.U_gam_unique` | `prop:Gs` |
| `Z3NetU.U_defN` | `def:Ns` |
| `Z3NetU.U_design` | `prop:F` |
| `Z3NetA.A_sep_rowScale` | `rem:projlines`, `thm:A` |

### `QUNets/Statements/ThmA.lean`

| Lean | paper |
|---|---|
| `Z3NetA.A_hom` | `thm:A` |
| `Z3NetA.A_net` | `thm:A` |
| `Z3NetA.A_covering` | `thm:A` |
| `Z3NetA.A_sep` | `thm:A` |
| `Z3NetA.A_sep_real` | `thm:A` |
| `Z3NetA.A_sep_eucl` | `thm:A` |
| `Z3NetA.covering_of_net` | `thm:A` |
| `Z3NetA.Ustar_adm` | `thm:A` |
| `Z3NetA.Ustar_reach` | `thm:A` |
| `Z3NetA.Ustar_data` | `thm:A` |
| `Z3NetA.Ustar_babai` | `thm:A`, `lem:babai` |
| `Z3NetA.Ustar_growth` | `thm:A`, `lem:babai` |
| `Z3NetA.aStar_le` | `thm:A`, `lem:babai` |
| `Z3NetA.aStar_three` | `thm:A`, `lem:babai` |
| `Z3NetA.Ainf_fin_le` | `thm:A` |
| `Z3NetA.prodAp_fin_le` | `thm:A` |
| `Z3NetA.Ainf_inf_le` | `thm:A` |
| `Z3NetA.prodAp_inf_le` | `thm:A` |
| `Z3NetA.hS_le_Hs` | `thm:A` |
| `Z3NetA.aStar_bound` | `thm:A` |
| `Z3NetA.aStar_bound_log` | `thm:A` |
| `Z3NetA.A_sharp` | `thm:A` |
| `Z3NetA.A_sharp_real` | `thm:A` |
| `Z3NetA.thmA` | `thm:A` |
| `Z3NetA.Apoint_indep` | `thm:A` |
| `Z3NetA.sat_poly` | `lem:sat` |
| `Z3NetA.sat_gamma` | `lem:sat` |
| `Z3NetA.sat_adm` | `lem:sat` |
| `Z3NetA.sat_basis` | `lem:sat` |
| `Z3NetA.sat_coset` | `lem:sat` |
| `Z3NetA.gamS_unique` | `lem:sat` |
| `Z3NetA.adelic_p` | `lem:adelic` |
| `Z3NetA.adelic_gamma` | `lem:adelic` |
| `Z3NetA.adelic_inf` | `lem:adelic` |
| `Z3NetA.adelic_proj` | `lem:adelic` |
| `Z3NetA.adelic_norm` | `lem:adelic` |
| `Z3NetA.hS_le_monic` | `lem:adelic` |
| `Z3NetA.babai` | `lem:babai` |
| `Z3NetA.babai_growth` | `lem:babai` |
| `Z3NetA.babai_flag` | `lem:babai` |
| `Z3NetA.Ustar_cols` | `def:Ustar` |
| `Z3NetA.Ustar_cols_unique` | `def:Ustar` |
| `Z3NetA.Ustar_round` | `def:Ustar` |
| `Z3NetA.Ustar_Msum` | `def:Ustar` |
| `Z3NetA.Ustar_dominant` | `def:Ustar` |
| `Z3NetA.Ustar_span` | `def:Ustar` |
| `Z3NetA.Ustar_proj` | `def:Ustar` |
| `Z3NetA.Ustar3_display` | `def:Ustar` |
| `Z3NetF.D_LB` | `prop:D`, `thm:U` |
| `Z3NetF.D_sep` | `prop:D`, `thm:U` |
| `Z3NetU.U_net` | `thm:U` |
| `Z3NetU.U_boxMinor` | `thm:U` |
| `Z3NetU.U_covering` | `thm:U` |
| `Z3NetU.U_sep` | `thm:U` |
| `Z3NetU.U_sep_real` | `thm:U` |
| `Z3NetU.U_aBound` | `thm:U` |
| `Z3NetU.U_a3` | `thm:U` |
| `Z3NetU.U_a4` | `thm:U` |
| `Z3NetU.U_a5` | `thm:U` |
| `Z3NetU.U_aLower` | `thm:U` |
| `Z3NetU.U_growth` | `thm:U` |
| `Z3NetU.U_sharp` | `thm:U` |
| `Z3NetU.U_sharp_real` | `thm:U` |
| `Z3NetU.U_logA_psi` | `thm:U` |
| `Z3NetU.U_growth_pnt` | `thm:U` |
| `Z3NetU.U_bound_growth_pnt` | `thm:U` |

### `QUNets/Statements/Skeleton.lean`

| Lean | paper |
|---|---|
| `Z3NetF.skelred_coord` | `lem:skelred` |
| `Z3NetF.skelred_sep` | `lem:skelred` |
| `Z3NetF.skelred_sep_real` | `lem:skelred` |
| `Z3NetF.skelred_carry` | `lem:skelred` |
| `Z3NetF.skelnec_N1` | `lem:skelnec` |
| `Z3NetF.skelnec_N2` | `lem:skelnec` |
| `Z3NetF.skelnec_N3_full` | `lem:skelnec` |
| `Z3NetF.skelnec_N3_skel` | `lem:skelnec` |
| `Z3NetF.skelcomp_normal` | `prop:skelcomp` |
| `Z3NetF.skel_Gs` | `prop:skelcomp`, `prop:Gs` |
| `Z3NetF.skel_reach_iff` | `prop:skelcomp`, `prop:F` |
| `Z3NetF.skelcomp_ii` | `prop:skelcomp` |
| `Z3NetF.skelcomp_iii` | `prop:skelcomp` |
| `Z3NetF.frameGraphK_spec` | (see the docstring) |
| `Z3NetF.skel_graphGen` | (see the docstring) |
| `Z3NetF.skelreach_iff` | `cor:skelreach`, `prop:skelcomp` |
| `Z3NetF.skelreach_nec` | `cor:skelreach` |
| `Z3NetF.skellat_L1` | `lem:skellat` |
| `Z3NetF.skellat_L1_attained` | `lem:skellat` |
| `Z3NetF.skellat_T` | `lem:skellat` |
| `Z3NetF.skellat_G` | `lem:skellat` |
| `Z3NetF.Bp_mono` | `def:G2rule` |
| `Z3NetF.G2N1_a` | `lem:G2N1` |
| `Z3NetF.G2N1_b` | `lem:G2N1` |
| `Z3NetF.G2N1_c` | `lem:G2N1` |
| `Z3NetF.codes_linf` | `rem:codes` |
| `Z3NetF.codes_l2` | `rem:codes` |
| `Z3NetF.codes_mds` | `rem:codes` |
| `Z3NetF.S2_net4` | `thm:S2` |
| `Z3NetF.S2_sep4` | `thm:S2` |
| `Z3NetF.S2_sep4_real` | `thm:S2` |
| `Z3NetF.S2_const4` | `thm:S2` |
| `Z3NetF.S2_net` | `thm:S2` |
| `Z3NetF.S2_sep` | `thm:S2` |
| `Z3NetF.S2_sep_real` | `thm:S2` |
| `Z3NetF.S2_thr` | `thm:S2` |
| `Z3NetF.S2_main58` | `thm:S2` |
| `Z3NetF.S2_eventually` | `thm:S2` |
| `Z3NetF.Bp_asymp` | `thm:S2` |
| `Z3NetF.frameid` | `lem:frameid` |
| `Z3NetF.frameid_cor` | `cor:frameid` |
| `Z3NetF.t3s4_reach` | `prop:t3s4`, `lem:box` |
| `Z3NetF.t3s4_net` | `prop:t3s4` |
| `Z3NetF.t3s4_sep` | `prop:t3s4` |
| `Z3NetF.t3s4_sep_real` | `prop:t3s4` |
| `Z3NetF.t3s4_M` | `prop:t3s4`, `tab:t3s4` |
| `Z3NetF.t3s4_main` | `prop:t3s4` |
| `Z3NetF.t3s4_table` | `tab:t3s4` |
| `Z3NetF.t3s4_lat` | `tab:t3s4` |
| `Z3NetF.t3s4_tab` | `tab:t3s4` |
| `Z3NetS1.L2s_min` | `lem:skellat` |
| `Z3NetS1.L2s_attained` | `lem:skellat` |
| `Z3NetS1.S1_net` | `thm:S1`, `def:S1` |
| `Z3NetS1.S1_sep` | `thm:S1`, `def:S1` |
| `Z3NetS1.S1_sep_real` | `thm:S1`, `def:S1` |
| `Z3NetS1.S1_const` | `thm:S1` |
| `Z3NetS1.S1_main` | `thm:S1` |
| `Z3NetS1.S1gen_net` | `thm:S1`, `def:S1`, `prop:skelcomp` |
| `Z3NetS1.S1_const_tendsto` | `thm:S1` |
| `Z3NetS1.S1_cells` | `thm:S1`, `lem:skellat` |
| `Z3NetS1.S1lat_index` | `thm:S1`, `lem:skellat` |
| `Z3NetS1.S1lat_min` | `thm:S1`, `lem:skellat` |
| `Z3NetS1.S1_opt` | `thm:S1`, `lem:skellat` |
| `Z3NetS1.S1_mu` | `thm:S1` |
| `Z3NetS1.S1_cover` | `thm:S1` |
| `Z3NetS1.S1_mesh` | `thm:S1` |
| `Z3NetS1.S1_mesh_tendsto` | `thm:S1` |

### `QUNets/Statements/Dim3.lean`

| Lean | paper |
|---|---|
| `Z3Net.P_boxMinor` | `thm:t0`, `thm:main` |
| `Z3Net.P_net` | `thm:t0`, `thm:main` |
| `Z3Net.cell_digits` | `prop:cell` |
| `Z3Net.cell_layer` | `prop:cell` |
| `Z3Net.lat3_cross` | `rem:lattice3` |
| `Z3Net.lat3_rot` | `rem:lattice3` |
| `Z3Net.lat3_decomp` | `rem:lattice3` |
| `Z3Net.lat3_det` | `rem:lattice3` |
| `Z3Net.lat3_norm` | `rem:lattice3` |
| `Z3Net.lat3_min` | `rem:lattice3` |
| `Z3Net.lat3_min_attained` | `rem:lattice3` |
| `Z3Net.lat3_cP` | `rem:lattice3` |
| `Z3Net.P_covering` | `thm:main` |
| `Z3Net.P_sep` | `thm:sep`, `thm:main` |
| `Z3Net.P_sep_ge8` | `thm:sep`, `thm:main` |
| `Z3Net.P_sep_real` | `thm:sep`, `thm:main` |
| `Z3NetC.colW_column` | `def:col`, `lem:drift` |
| `Z3NetC.col_column` | `def:col` |
| `Z3NetC.colmin` | `thm:colmin` |
| `Z3NetC.colmin_real` | `thm:colmin` |
| `Z3NetC.col_net` | `thm:col` |
| `Z3NetC.col_covering` | `thm:col` |
| `Z3NetC.col_mindist` | `thm:col` |
| `Z3NetC.col_closest` | `thm:col` |
| `Z3NetC.col_expansion` | `thm:col` |
| `Z3NetC.col_sep_real` | `thm:col` |
| `Z3NetC.col_mono` | `thm:col` |
| `Z3NetC.col_values` | `thm:col` |
| `Z3NetC.col_boxMinor_int` | `thm:col` |
| `Z3NetC.shared_count` | `lem:shared` |
| `Z3NetC.shared_fun` | `lem:shared` |
| `Z3NetC.colfree` | `prop:colfree` |
| `Z3NetC.colshift_eq` | `prop:colshift` |
| `Z3NetC.colshift_agree2` | `prop:colshift` |
| `Z3NetC.colshift_lower` | `prop:colshift` |
| `Z3NetC.colshift_upper` | `prop:colshift` |
| `Z3NetC.colshift_eq_eucl` | `prop:colshift` |
| `Z3NetKN.B2gen_net` | `def:B`, `prop:Bnet` |
| `Z3NetKN.B1gen_net` | `def:B`, `prop:Bnet` |
| `Z3NetKN.B2_net` | `rem:B2`, `thm:S1`, `def:B`, `prop:Bnet`, `thm:allm`, `cor:allm` |
| `Z3NetKN.B2_sep` | `rem:B2`, `thm:S1`, `def:B`, `prop:Bnet`, `thm:allm`, `cor:allm` |
| `Z3NetKN.B2_skel_iff` | `rem:B2` |
| `Z3NetKN.B2_rem_sep` | `rem:B2` |
| `Z3NetKN.B2_rem_sep_real` | `rem:B2` |
| `Z3NetKN.B2_relax` | `rem:B2` |
| `Z3NetKN.B2_const` | `rem:B2` |
| `Z3NetKN.B1_net` | `thm:allm`, `def:B`, `prop:Bnet` |
| `Z3NetKN.B1_sep` | `thm:allm`, `def:B`, `prop:Bnet` |
| `Z3NetKN.B1_rho_spec` | `thm:allm` |
| `Z3NetKN.B1_sep_real` | `thm:allm` |
| `Z3NetKN.B1_tendsto` | `thm:allm` |
| `Z3NetKN.B1_rho27` | `thm:allm` |
| `Z3NetKN.B1_gt09` | `thm:allm` |
| `Z3NetKN.B1_g_lt` | `thm:allm` |
| `Z3NetKN.gB1_strictMonoOn` | `thm:allm` |
| `Z3NetKN.gB1_tendsto` | `thm:allm` |
| `Z3NetKN.gB1_27` | `thm:allm` |
| `Z3NetKN.cor_allm` | `cor:allm` |
| `Z3NetKN.bndDim3_gt` | `cor:allm` |
| `Z3NetKN.bndDim3_tendsto` | `cor:allm` |
| `Z3NetKN.cor_allm_mesh` | `cor:allm` |
| `Z3NetKN.cor_allm_mesh2` | `cor:allm` |
| `Z3NetKN.cor_allm_consts` | `cor:allm` |
| `Z3NetKN.KN1_net` | `rem:perprime`, `prop:pp1`, `prop:pp2`, `def:ppdesign` |
| `Z3NetKN.KN1_sep` | `rem:perprime`, `prop:ppsep` |
| `Z3NetKN.KN2_net` | `rem:perprime`, `prop:pp1`, `prop:pp2`, `def:ppdesign` |
| `Z3NetKN.KN2_sep` | `rem:perprime`, `prop:ppsep` |

### `QUNets/Statements/Base23.lean`

| Lean | paper |
|---|---|
| `Z3Net.base2_net` | `rem:base2` |
| `Z3NetB23.lift_net` | `lem:lift` |
| `Z3NetB23.lift_exists` | `lem:lift` |
| `Z3NetB23.liftsep` | `lem:liftsep` |
| `Z3NetB23.shiftcert_a` | `lem:shiftcert` |
| `Z3NetB23.vcirc_eq_iInf` | `lem:shiftcert` |
| `Z3NetB23.shiftcert_b` | `lem:shiftcert` |
| `Z3NetB23.b23_seed` | `thm:base23`, `tab:b23seeds` |
| `Z3NetB23.b23_lift` | `thm:base23` |
| `Z3NetB23.b23_vcirc` | `thm:base23`, `tab:base23` |
| `Z3NetB23.base23_net` | `thm:base23` |
| `Z3NetB23.base23_exists` | `thm:base23` |
| `Z3NetB23.base23_everyshift` | `thm:base23`, `tab:base23` |
| `Z3NetB23.base23_everyshift_base` | `thm:base23` |
| `Z3NetB23.base23_witcur` | `thm:base23` |
| `Z3NetB23.base23_shifted` | `thm:base23` |
| `Z3NetB23.shiftparity_parity` | `rem:shiftparity` |
| `Z3NetB23.shiftparity_first_even` | `rem:shiftparity` |
| `Z3NetB23.shiftparity_dichotomy` | `rem:shiftparity` |
| `Z3NetB23.shiftparity_floor_iff` | `rem:shiftparity` |
| `Z3NetB23.shiftparity_tendsto` | `rem:shiftparity` |

### `QUNets/Statements/DGS.lean`

| Lean | paper |
|---|---|
| `Z3NetF.shift_net` | `lem:shift` |
| `Z3NetF.digPointShift_net` | `lem:shift` |
| `Z3NetF.shift_graph` | `lem:shift` |
| `Z3NetF.shift_graph_cells` | `lem:shift` |
| `Z3NetF.Ss_coord_shift` | `prop:shift` |
| `Z3NetF.Ss_sep_shift` | `prop:shift` |
| `Z3NetF.D_sep_shift` | `prop:shift` |
| `Z3NetF.S2_sep4_shift` | `prop:shift` |
| `Z3NetF.S2_sep4_shift_real` | `prop:shift` |
| `Z3NetF.S2_sep_shift` | `prop:shift` |
| `Z3NetF.S2_sep_shift_real` | `prop:shift` |
| `Z3NetA.Apoint_eq_AGen` | `prop:shift` |
| `Z3NetA.A_net_shift` | `prop:shift` |
| `Z3NetA.A_sep_shift` | `prop:shift` |
| `Z3NetA.A_sep_shift_real` | `prop:shift` |
| `Z3NetA.A_sep_shift_eucl` | `prop:shift` |
| `Z3NetA.A_sharp_shift` | `prop:shift` |
| `Z3NetA.A_sharp_shift_real` | `prop:shift` |
| `Z3Net.P_sep_shift` | `prop:shift` |
| `Z3Net.P_sep_shift_ge8` | `prop:shift` |
| `Z3Net.P_sep_shift_real` | `prop:shift` |
| `Z3NetS1.S1_sep_shift` | `prop:shift` |
| `Z3NetS1.S1_sep_shift_real` | `prop:shift` |
| `Z3NetS1.S1_cells_shift` | `prop:shift` |
| `Z3NetS1.S1_cover_shift` | `prop:shift` |
| `Z3NetKN.B1_sep_shift` | `prop:shift` |
| `Z3NetKN.B1_sep_shift_real` | `prop:shift` |
| `Z3NetKN.B2_rem_sep_shift_real` | `prop:shift` |
| `Z3NetKN.allmshift` | `cor:allmshift` |
| `Z3NetHL.GF_relax_shift` | `prop:shift` |
| `Z3NetHL.GF_dom_shift` | `prop:shift` |
| `Z3NetHL.GF_dom_shift_real` | `prop:shift` |
| `Z3NetHL.HL_relax_shift` | `prop:shift` |
| `Z3NetHL.HL_dom_shift` | `prop:shift` |
| `Z3NetHL.HL_dom_shift_real` | `prop:shift` |
| `Z3NetHL.HL_domL_shift_real` | `prop:shift` |
| `Z3NetHL.HL_main_shift_real` | `prop:shift` |
| `Z3NetHL.HL_main_shift` | `prop:shift` |
| `Z3NetHL.GFpoint_shift_zero` | `prop:shift` |
| `Z3NetHL.HLpoint_shift_zero` | `prop:shift` |
| `Z3NetC.allmshift_m3` | `cor:allmshift` |
| `Z3NetC.shiftshared_col` | `rem:shiftshared` |
| `QUNetsM3.W_shift` | `rem:wshift`, `prop:wnet` |
| `QUNetsM3.digitalPtS_eq_dshiftPt` | `rem:wshift`, `def:dshift` |
| `Z3NetDGS.lemma37` | `cor:dgs` |
| `Z3NetDGS.lemma37_strict` | `cor:dgs` |
| `Z3NetDGS.isTMSNet_of_isNet0` | `cor:dgs` |
| `Z3NetDGS.dgsNet_eq` | `cor:dgs` |
| `Z3NetDGS.dgs_main` | `cor:dgs` |
| `Z3NetDGS.dgs_P` | `cor:dgs` |
| `Z3NetDGS.dgs_A` | `cor:dgs` |
| `Z3NetDGS.dgs_S1` | `cor:dgs` |
| `Z3NetDGS.dgs_HL` | `cor:dgs` |
| `Z3NetDGS.dgs_allm` | `cor:dgs` |
| `Z3NetDGS.dgs_S1_floor` | `cor:dgs` |
| `Z3NetDGS.dgsfinite_sep` | `rem:dgsfinite` |
| `Z3NetDGS.frame3_net` | `rem:dgsfinite` |
| `Z3NetDGS.dgs_family` | `rem:dgsfinite` |
| `Z3NetDGS.dgs_pp` | `rem:dgsfinite` |
| `Z3NetDGS.dgs_family_pp` | `rem:dgsfinite` |
| `Z3NetDGS.dgs_family_b23` | `rem:dgsfinite`, `cor:dgs`, `thm:base23` |
| `Z3NetDGS.dgs_family_all` | `rem:dgsfinite` |
| `Z3NetDGS.linf_dist` | `prop:linf` |
| `Z3NetDGS.linf_mesh` | `prop:linf` |

### `QUNets/Statements/Deficit.lean`

| Lean | paper |
|---|---|
| `Z3NetF.Kdef_ne_top_iff` | `def:K` |
| `Z3NetF.Kdef_eq_Kexp` | `def:K` |
| `Z3NetF.K_expansion` | `def:K` |
| `Z3NetF.Dprime_LB` | `prop:Dprime` |
| `Z3NetF.Dprime` | `prop:Dprime` |
| `Z3NetF.Dprime_sep` | `prop:Dprime` |
| `Z3NetF.Kone` | `lem:Kone` |
| `Z3NetF.ceils_neg` | `cor:ceils` |
| `Z3NetF.ceils_pos` | `cor:ceils` |
| `Z3NetF.ceils_pos_C` | `cor:ceils` |
| `Z3NetF.D4D2_data` | `prop:4D2`, `prop:Gs` |
| `Z3NetF.D4D2_net` | `prop:4D2` |
| `Z3NetF.D4D2_boxMinor` | `prop:4D2` |
| `Z3NetF.D4D2_covering` | `prop:4D2` |
| `Z3NetF.D4D2_KS` | `prop:4D2` |
| `Z3NetF.D4D2_LB_small` | `prop:4D2` |
| `Z3NetF.D4D2_LB` | `prop:4D2` |
| `Z3NetF.D4D2_sep` | `prop:4D2` |
| `Z3NetF.D4D2_sep_eucl` | `prop:4D2` |
| `Z3NetF.D4D2_ceil` | `prop:4D2` |
| `Z3NetF.D4D2_ceil_real` | `prop:4D2` |
| `Z3NetF.pm1_ring` | `rem:pm1` |
| `Z3NetF.pm1` | `rem:pm1` |
| `Z3NetF.k1_sep` | `prop:k1` |
| `Z3NetF.k1_sep_eucl` | `prop:k1` |
| `Z3NetF.k1_tail` | `prop:k1` |
| `Z3NetF.k1_transfer` | `prop:k1` |
| `Z3NetF.k1_Ns_sep` | `prop:k1` |
| `Z3NetF.k1_ceil` | `prop:k1` |
| `Z3NetF.k1_ceil_eucl` | `prop:k1` |
| `Z3NetF.k1_ceil_real` | `prop:k1` |
| `Z3NetF.k1designs_frame_K` | `prop:k1designs` |
| `Z3NetF.k1designs_frame6_cauchy` | `prop:k1designs` |
| `Z3NetF.k1designs_free_K` | `prop:k1designs` |
| `Z3NetF.k1designs_free5_net` | `prop:k1designs` |
| `Z3NetF.k1designs_free6a_net` | `prop:k1designs` |
| `Z3NetF.k1designs_free6b_net` | `prop:k1designs`, `tab:practical` |
| `Z3NetF.k1designs_frame5_cauchy` | `prop:k1designs`, `tab:Kdesigns` |
| `Z3NetF.P2_ceiling` | `prop:P2` |
| `Z3NetF.P2_forward` | `prop:P2` |
| `Z3NetF.P2_forward_C` | `prop:P2` |
| `Z3NetF.Ktrue_ceiling` | `def:Ktrue` |
| `Z3NetF.L_Kpair` | `thm:L` |
| `Z3NetF.L_ceiling` | `thm:L` |
| `Z3NetF.L_pm1` | `thm:L` |
| `Z3NetF.O5_Kpair` | `thm:O5` |
| `Z3NetF.O5_sep` | `thm:O5` |
| `Z3NetF.O_orient` | `lem:O` |
| `Z3NetF.E_lcm` | `prop:E` |
| `Z3NetF.E_two_pow` | `prop:E` |
| `Z3NetF.E_Ustar` | `prop:E` |
| `Z3NetF.C_count` | `lem:C` |
| `Z3NetF.C_count_sharp` | `lem:C` |
| `Z3NetF.PGLImage_self` | `thm:Lstar` |
| `Z3NetF.Lstar_bound` | `thm:Lstar` |
| `Z3Net.ceil_neg` | `prop:ceil` |
| `Z3Net.ceil_pos` | `prop:ceil` |
| `Z3Net.propA_neg` | `prop:A` |
| `Z3Net.propA_pos` | `prop:A` |
| `Z3Net.propA_pos_k2` | `prop:A` |
| `Z3Net.sign_boxMinor` | `rem:sign`, `prop:ceil` |
| `Z3Net.sign_net` | `rem:sign`, `prop:ceil` |
| `Z3Net.sign_graph` | `rem:sign`, `prop:ceil` |
| `Z3Net.sign_cap` | `rem:sign`, `prop:ceil` |
| `Z3NetA.k1designs_frame4_Ustar` | `prop:k1designs` |
| `Z3NetC.drift_step` | `lem:drift` |
| `Z3NetC.drift_cycle` | `lem:drift` |
| `Z3NetC.drift_range` | `lem:drift` |
| `Z3NetC.drift_eta` | `lem:drift` |
| `Z3NetC.drift_net` | `lem:drift` |
| `Z3NetC.drift_excess` | `lem:drift` |
| `Z3NetC.colceil` | `cor:colceil` |
| `Z3NetC.colO_net_iff` | `thm:O` |
| `Z3NetC.colO_even` | `thm:O` |
| `Z3NetC.colO_opt` | `thm:O` |

### `QUNets/Statements/WhyLat.lean`

| Lean | paper |
|---|---|
| `Z3NetF.hom_iff` | `lem:hom` |
| `Z3NetF.linoff_a` | `cor:linoff` |
| `Z3NetF.linoff_b` | `cor:linoff` |
| `Z3NetF.linoff_c` | `cor:linoff` |
| `Z3NetF.phase_i` | `lem:phase` |
| `Z3NetF.phase_i_free` | `lem:phase` |
| `Z3NetF.phase_ii` | `lem:phase` |
| `Z3NetF.phase_ii_rank` | `lem:phase` |
| `Z3NetF.cube_i` | `prop:cube` |
| `Z3NetF.cube_ii` | `prop:cube` |
| `Z3NetF.cube_iii` | `prop:cube` |
| `Z3NetF.cube_iv_rat` | `prop:cube` |
| `Z3NetF.cube_iv_min` | `prop:cube` |
| `Z3NetF.cube_iv_vals` | `prop:cube` |

### `QUNets/Statements/Large.lean`

| Lean | paper |
|---|---|
| `Z3NetF.S1E_net` | `prop:S1E` |
| `Z3NetF.S1E_sep` | `prop:S1E` |
| `Z3NetF.S1E_sep_real` | `prop:S1E` |
| `Z3NetF.S1E_lam2` | `prop:S1E` |
| `Z3NetF.S1E_tab_s8_p10007_rho` | `prop:S1E`, `tab:S1E` |
| `Z3NetF.S1E_tab_s3_p1009` | `tab:S1E` |
| `Z3NetF.S1E_tab_s3_p10007` | `tab:S1E` |
| `Z3NetF.S1E_tab_s3_p1000003` | `tab:S1E` |
| `Z3NetF.S1E_tab_s3_p100000007` | `tab:S1E` |
| `Z3NetF.S1E_tab_s3_p996001` | `tab:S1E` |
| `Z3NetF.S1E_tab_s3_p10002435263` | `tab:S1E` |
| `Z3NetF.S1E_tab_s4_p1009` | `tab:S1E` |
| `Z3NetF.S1E_tab_s4_p10007` | `tab:S1E` |
| `Z3NetF.S1E_tab_s4_p1000003` | `tab:S1E` |
| `Z3NetF.S1E_tab_s4_p100000007` | `tab:S1E` |
| `Z3NetF.S1E_tab_s4_p1006301` | `tab:S1E` |
| `Z3NetF.S1E_tab_s4_p10040205517` | `tab:S1E` |
| `Z3NetF.S1E_tab_s5_p1009` | `tab:S1E` |
| `Z3NetF.S1E_tab_s5_p10007` | `tab:S1E` |
| `Z3NetF.S1E_tab_s5_p1000003` | `tab:S1E` |
| `Z3NetF.S1E_tab_s5_p100000007` | `tab:S1E` |
| `Z3NetF.S1E_tab_s5_p1025909` | `tab:S1E` |
| `Z3NetF.S1E_tab_s5_p10123347709` | `tab:S1E` |
| `Z3NetF.S1E_tab_s6_p1009` | `tab:S1E` |
| `Z3NetF.S1E_tab_s6_p10007` | `tab:S1E` |
| `Z3NetF.S1E_tab_s6_p1000003` | `tab:S1E` |
| `Z3NetF.S1E_tab_s6_p100000007` | `tab:S1E` |
| `Z3NetF.S1E_tab_s6_p1033493` | `tab:S1E` |
| `Z3NetF.S1E_tab_s6_p10136355487` | `tab:S1E` |
| `Z3NetF.S1E_tab_s7_p1009` | `tab:S1E` |
| `Z3NetF.S1E_tab_s7_p10007` | `tab:S1E` |
| `Z3NetF.S1E_tab_s7_p1000003` | `tab:S1E` |
| `Z3NetF.S1E_tab_s7_p100000007` | `tab:S1E` |
| `Z3NetF.S1E_tab_s7_p1138273` | `tab:S1E` |
| `Z3NetF.S1E_tab_s7_p10660100951` | `tab:S1E` |
| `Z3NetF.S1E_tab_s8_p1009` | `tab:S1E` |
| `Z3NetF.S1E_tab_s8_p10007` | `tab:S1E` |
| `Z3NetF.S1E_tab_s8_p1000003` | `tab:S1E` |
| `Z3NetF.S1E_tab_s8_p100000007` | `tab:S1E` |
| `Z3NetF.S1E_tab_s8_p1071337` | `tab:S1E` |
| `Z3NetF.S1E_tab_s8_p11556622703` | `tab:S1E` |
| `QUNetsM3.TC_params` | `prop:twocoset` |
| `QUNetsM3.TC_cells` | `prop:twocoset` |
| `QUNetsM3.TC_net` | `prop:twocoset` |
| `QUNetsM3.TC_freeJitter` | `prop:twocoset` |
| `QUNetsM3.TC_sep` | `prop:twocoset` |
| `QUNetsM3.TC_sep_real` | `prop:twocoset` |
| `QUNetsM3.TC_bound` | `prop:twocoset` |
| `QUNetsM3.TC_pair` | `prop:twocoset` |
| `QUNetsM3.TC_pair_lt` | `prop:twocoset` |
| `QUNetsM3.TC_delta` | `prop:twocoset` |
| `QUNetsM3.TC_limit` | `prop:twocoset` |
| `QUNetsM3.W_layer` | `prop:wnet`, `rem:wstar` |
| `QUNetsM3.W_net` | `prop:wnet` |
| `QUNetsM3.W_cells` | `prop:wnet` |
| `QUNetsM3.W_freeJitter` | `prop:wnet` |
| `QUNetsM3.W_sep` | `prop:wnet` |
| `QUNetsM3.W_sep_real` | `prop:wnet` |
| `QUNetsM3.W_bound` | `prop:wnet` |
| `QUNetsM3.W_pair` | `prop:wnet` |
| `QUNetsM3.W_pair_lt` | `prop:wnet` |
| `QUNetsM3.W_delta` | `prop:wnet` |
| `QUNetsM3.W_limit` | `prop:wnet` |
| `QUNetsM3.W_exact` | `prop:wnet` |
| `QUNetsM3.W_four` | `prop:wnet` |
| `QUNetsM3.W_least` | `prop:wnet` |
| `QUNetsM3.W_wrap` | `lem:wwrap` |
| `QUNetsM3.Wfam_star` | `prop:wfamily`, `rem:wstar` |
| `QUNetsM3.Wfam_one` | `prop:wfamily` |
| `QUNetsM3.Wfam_two` | `prop:wfamily` |
| `QUNetsM3.Wfam_three_tau` | `prop:wfamily` |
| `QUNetsM3.Wfam_three` | `prop:wfamily` |
| `QUNetsM3.Wstar_net` | `rem:wstar` |
| `QUNetsM3.Wstar_rho` | `rem:wstar` |
| `QUNetsM3.Wstar_eps` | `rem:wstar` |
| `QUNetsM3.Wstar_bound` | `rem:wstar` |
| `QUNetsM3.Wstar_limit` | `rem:wstar` |
| `QUNetsM3.Wstar_thresholds` | `rem:wstar` |
| `QUNetsM3.Wstar_ahead` | `rem:wstar` |
| `QUNetsM3.TC_shift` | `rem:wshift`, `prop:twocoset` |
| `QUNetsM3.W_wrap_one` | `rem:wshift`, `lem:wwrap` |

### `QUNets/Statements/Split.lean`

| Lean | paper |
|---|---|
| `Z3NetF.P_half_mod` | `prop:P` |
| `Z3NetF.P_half_mod_large` | `prop:P` |
| `Z3NetF.P_half_rat` | `prop:P` |
| `Z3NetF.Tsplit_minor` | `lem:Tsplit` |
| `Z3NetF.Tsplit_net_iff` | `lem:Tsplit` |
| `Z3NetF.Tsplit_prime_bound` | `lem:Tsplit` |
| `Z3NetF.split_spec` | `lem:Tsplit` |
| `Z3NetF.split_boxMinor` | `lem:Tsplit` |
| `Z3NetF.Rsplit_row0` | `lem:Rsplit` |
| `Z3NetF.Gsplit_normal` | `prop:Gsplit` |
| `Z3NetF.Gsplit_nodes` | `prop:Gsplit` |
| `Z3NetF.Gsplit_beta` | `prop:Gsplit`, `prop:Gs` |
| `Z3NetF.Gsplit_gauge` | `prop:Gsplit`, `prop:Gs` |
| `Z3NetF.Gsplit_row0` | `prop:Gsplit`, `prop:Gs` |
| `Z3NetF.Gsplit_tsk_unit` | `prop:Gsplit`, `def:Ns`, `cor:tsk` |
| `Z3NetF.Gsplit_tsk_net` | `prop:Gsplit`, `def:Ns`, `cor:tsk` |
| `Z3NetF.Gsplit_reach_iff` | `prop:Gsplit`, `prop:F` |
| `Z3NetF.Gsplit_poly_iff` | `prop:Gsplit`, `prop:F` |
| `Z3NetHL.HL_frameMinor` | `lem:Tsplit` |
| `Z3NetHL.HL_propN` | `prop:Gsplit` |
| `Z3NetHL.HL_row0` | `prop:Gsplit` |
| `Z3NetHL.HL_net` | `prop:Gsplit` |
| `Z3NetHL.HL_rowDesign` | `prop:Gsplit` |
| `Z3NetHL.HL_row0_lev` | `prop:Gsplit` |
| `Z3NetHL.HL_net_lev` | `prop:Gsplit` |
| `Z3NetHL.HL_relax_lev` | `prop:Gsplit` |
| `Z3NetHL.HL_dom_lev` | `prop:Gsplit` |
| `Z3NetHL.HL_dom_lev_real` | `prop:Gsplit` |
| `Z3NetHL.HL_halfDesign` | `lem:Hs` |
| `Z3NetHL.HL_Hs` | `lem:Hs` |
| `Z3NetHL.HL_relax` | `prop:Hk` |
| `Z3NetHL.HL_dom` | `prop:Hk` |
| `Z3NetHL.HL_dom_real` | `prop:Hk` |
| `Z3NetHL.GF_relax` | `prop:Hk` |
| `Z3NetHL.GF_dom` | `prop:Hk` |
| `Z3NetHL.GF_dom_real` | `prop:Hk` |
| `Z3NetHL.GF_upper` | `prop:Hk` |
| `Z3NetHL.HL_domL_real` | `prop:Hk` |
| `Z3NetHL.HL_main` | `thm:HL`, `lem:Hs` |
| `Z3NetHL.HL_main_real` | `thm:HL`, `lem:Hs` |
| `Z3NetHL.HL_upper` | `thm:HL` |
| `Z3NetHL.HL_limit` | `thm:HL` |
| `Z3NetHL.HL_Bbound` | `thm:HL` |
| `Z3NetHL.R2_sep` | `lem:R2` |
| `Z3NetHL.halfPhi_row` | `prop:half` |
| `Z3NetHL.half_sep` | `prop:half` |
| `Z3NetHL.half_LB2_ge` | `prop:half` |
| `Z3NetHL.half_lam_le` | `prop:half` |
| `Z3NetHL.half_lam_dom` | `prop:half` |
| `Z3NetHL.half_upper` | `prop:half`, `prop:Hk` |
| `Z3NetHL.half_limit` | `prop:half`, `prop:Hk` |
| `Z3NetHL.half_net_generic` | `prop:half` |
| `Z3NetHL.half_M_exists` | `prop:half` |
| `Z3NetHL.qstar_net` | `prop:half5` |
| `Z3NetHL.qstar_sep` | `prop:half5` |
| `Z3NetHL.qstar_bounds` | `prop:half5` |
| `Z3NetHL.qstar_limit` | `prop:half5` |
| `Z3NetHL.qstar_hk` | `prop:half5` |
| `Z3NetHL.sepN_spec` | `rem:accounting` |
| `Z3NetHL.ell2_eq_halfEllInf` | `rem:accounting`, `prop:half5` |
| `Z3NetHL.acct_upper` | `rem:accounting` |
| `Z3NetHL.acct_lower` | `rem:accounting` |
| `Z3NetHL.acct_main` | `rem:accounting` |
| `Z3NetHL.acct_liminf` | `rem:accounting` |
| `Z3NetHL.acct_exact` | `rem:accounting` |
| `Z3NetHL.acct_qstar` | `rem:accounting` |
| `Z3NetHL.acct_counterexample` | `rem:accounting` |
| `Z3NetHL.acct_LB2` | `rem:accounting` |
| `Z3NetHL.acct_LBHk` | `rem:accounting`, `prop:Hk` |
| `Z3NetHL.thmD` | `thm:D` |
| `Z3NetHL.thmD_star` | `thm:D` |
| `Z3NetHL.thmD_skew` | `thm:D` |
| `Z3NetHL.thmD_conj` | `thm:D` |
| `Z3NetHL.B5_design` | `prop:HL5`, `app:designs` |
| `Z3NetHL.B5_net` | `prop:HL5`, `app:designs` |
| `Z3NetHL.B5_sep` | `prop:HL5`, `app:designs` |
| `Z3NetHL.B5_sep_real` | `prop:HL5`, `app:designs` |
| `Z3NetHL.B5_net_lev` | `prop:HL5` |

### `QUNets/Statements/Appendix.lean`

| Lean | paper |
|---|---|
| `Z3NetKN.pp2_table` | `app:perprime` |
| `Z3NetKN.pp1_table` | `app:perprime` |
| `Z3NetKN.pp2_net` | `prop:pp2` |
| `Z3NetKN.pp1_net` | `prop:pp1` |
| `Z3NetKN.ppsep_shift` | `rem:ppshift` |
| `Z3NetKN.KN1_sep_shift` | `rem:ppshift`, `tab:perprime` |
| `Z3NetKN.KN2_sep_shift` | `rem:ppshift`, `tab:perprime` |
| `Z3NetPI.ppinv_window` | `lem:ppinv`, `lem:box` |
| `Z3NetPI.ppinv_a2` | `lem:ppinv` |
| `Z3NetPI.ppinv_a1` | `lem:ppinv` |
| `Z3NetPI.ppinv_b2` | `lem:ppinv` |
| `Z3NetPI.ppinv_b1` | `lem:ppinv` |
| `Z3NetKN.pp1_net_all` | `prop:pp1` |
| `Z3NetKN.ppsep_general` | `prop:ppsep`, `def:pprelax` |

## Labels formalized as definitions only

These labels are formalized as definitions (the `*Defs` modules), used by the compared theorems.

| label | kind | Lean |
|---|---|---|
| `def:K` | definitions | `Z3NetF.jit`, `Z3NetF.cost`, `Z3NetF.Kdef`, `Z3NetF.Sdef`, `Z3NetF.cfgs`, `Z3NetF.sigma`, `Z3NetF.bwd` |
| `def:S2` | definitions | `Z3NetF.IsS2skel`, `Z3NetF.S2A` |
| `def:Ustar` | definitions | `Z3NetA.ProjCoef`, `Z3NetA.IsUstarCols`, `Z3NetA.Ecol`, `Z3NetA.alphaS`, `Z3NetA.aStar`, `Z3NetA.UstarF` |
| `def:lift` | definitions | `Z3NetB23.Zsub`, `Z3NetB23.pairSub`, `Z3NetB23.Admissible`, `Z3NetB23.VanishTop`, `Z3NetB23.liftGen`, `Z3NetB23.liftShift`, `Z3NetB23.LiftChain` |
| `def:net` | definitions | `Z3Net.tau`, `Z3Net.T`, `Z3Net.K`, `Z3Net.E`, `Z3Net.L`, `Z3Net.PGen`, `Z3Net.Ppoint` |
| `def:pprelax` | definitions | `Z3NetKN.rlxLin`, `Z3NetKN.rlxRes`, `Z3NetKN.rlxT`, `Z3NetKN.rlxTerm`, `Z3NetKN.IsPPCert` |
| `def:split` | definitions | `Z3NetF.splitRead`, `Z3NetF.SplitOK`, `Z3NetF.splitGraph` |
| `lem:adelic` | definitions | `Z3NetA.colE`, `Z3NetA.polyVecR`, `Z3NetA.polyVecQ`, `Z3NetA.Vlt`, `Z3NetA.lineA`, `Z3NetA.piA`, `Z3NetA.AinfSet`, `Z3NetA.Ainf`, `Z3NetA.ApSet`, `Z3NetA.Ap`, `Z3NetA.primesS`, `Z3NetA.hS` |
| `lem:sat` | definitions | `Z3NetA.RS`, `Z3NetA.InRS`, `Z3NetA.SUnit`, `Z3NetA.wQ`, `Z3NetA.yQ`, `Z3NetA.colPoly`, `Z3NetA.InLam`, `Z3NetA.kappa`, `Z3NetA.gamS`, `Z3NetA.AdmCol` |
| `prop:Dprime` | definitions | `Z3NetF.QD` |
| `thm:A` | definitions | `Z3NetA.placeA`, `Z3NetA.AdmBase`, `Z3NetA.UstarR`, `Z3NetA.UrS`, `Z3NetA.betaS`, `Z3NetA.Apoint` |

(2 compared theorems carry their paper reference in the docstring only.)
