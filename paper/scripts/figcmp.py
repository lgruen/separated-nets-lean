#!/usr/bin/env python3
r"""figcmp.py -- compare regenerated figures with the committed ones.

    python scripts/figcmp.py NEWDIR [REFDIR]        (REFDIR default: figs/ next to scripts/)

For every PDF of REFDIR that core.tex includes (\includegraphics{figs/...} and \arcfig{...}, found in core.tex at run
time) and for the generated caption files arc_captions.tex, part1_captions.tex, col_captions.tex, w_captions.tex: IDENTICAL if the bytes agree; otherwise both
PDFs are rasterized with pdftoppm (poppler, 150 dpi) and compared pixel by pixel: SAME-PIXELS or DIFFERENT.
(PDF bytes depend on the matplotlib version and, without fixed metadata, on the date; the drawn content does not.)
Without pdftoppm a byte difference is reported as NOT-COMPARED.  Exit status 1 if anything is DIFFERENT or missing,
or if a caption file differs.  Needs numpy + matplotlib (PNG reader) only when pixels are compared.
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.dirname(HERE)
CAPTIONS = ('arc_captions.tex', 'part1_captions.tex', 'col_captions.tex', 'w_captions.tex')   # written by figs_arc.py, figs_part1.py, figs_col.py, figs_wnet.py


def included_figs():
    tex = open(os.path.join(PAPER, 'core.tex')).read()
    names = set(re.findall(r'\\includegraphics(?:\[[^\]]*\])?\{figs/([^}]+)\.pdf\}', tex))
    names |= set(re.findall(r'\\arcfig\{([^}]+)\}', tex))
    names.discard('#1')
    return sorted(names)


def raster(pdf, outdir, tag):
    base = os.path.join(outdir, tag)
    subprocess.run(['pdftoppm', '-r', '150', '-png', pdf, base], check=True)
    return sorted(os.path.join(outdir, f) for f in os.listdir(outdir) if f.startswith(tag) and f.endswith('.png'))


def pixels_equal(a, b):
    import numpy as np
    import matplotlib.image as mi
    tmp = tempfile.mkdtemp(prefix='figcmp_')
    try:
        ra, rb = raster(a, tmp, 'a'), raster(b, tmp, 'b')
        if len(ra) != len(rb):
            return False, 'page count differs'
        for x, y in zip(ra, rb):
            X, Y = mi.imread(x), mi.imread(y)
            if X.shape != Y.shape:
                return False, f'size {X.shape} vs {Y.shape}'
            d = np.abs(X.astype(float) - Y.astype(float))
            if d.max() > 0:
                return False, f'{int((d.max(-1) > 0).sum())} pixels differ (max {d.max():.3f})'
        return True, ''
    finally:
        shutil.rmtree(tmp)


def main():
    new = os.path.abspath(sys.argv[1])
    ref = os.path.abspath(sys.argv[2]) if len(sys.argv) > 2 else os.path.join(PAPER, 'figs')
    have_raster = shutil.which('pdftoppm') is not None
    bad = 0
    for n in included_figs():
        a, b = os.path.join(new, n + '.pdf'), os.path.join(ref, n + '.pdf')
        if not os.path.exists(a):
            print(f'  MISSING      {n}.pdf (not regenerated)'); bad += 1; continue
        if open(a, 'rb').read() == open(b, 'rb').read():
            print(f'  IDENTICAL    {n}.pdf'); continue
        if not have_raster:
            print(f'  NOT-COMPARED {n}.pdf (bytes differ; pdftoppm not found)'); continue
        ok, why = pixels_equal(a, b)
        print(f'  {"SAME-PIXELS " if ok else "DIFFERENT   "} {n}.pdf {why}')
        bad += not ok
    for cap in CAPTIONS:
        a, b = os.path.join(new, cap), os.path.join(ref, cap)
        same = os.path.exists(a) and open(a).read() == open(b).read()
        print(f'  {"IDENTICAL   " if same else ("DIFFERENT   " if os.path.exists(a) else "MISSING     ")} {cap}')
        bad += not same
    print('figcmp:', 'all figures agree' if not bad else f'{bad} DIFFERENCE(S)')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
