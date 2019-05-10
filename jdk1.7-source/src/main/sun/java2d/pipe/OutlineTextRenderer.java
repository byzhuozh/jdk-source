/*
 * Copyright (c) 2000, 2005, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package sun.java2d.pipe;

import java.awt.font.FontRenderContext;
import java.awt.font.GlyphVector;
import java.awt.font.TextLayout;
import sun.java2d.SunGraphics2D;
import sun.font.GlyphList;
import sun.awt.SunHints;

import java.awt.Shape;
import java.awt.geom.AffineTransform;
import java.awt.font.TextLayout;

/**
 * A delegate pipe of SG2D for drawing "large" text with
 * a solid source colour to an opaque destination.
 * The text is drawn as a filled outline.
 * Since the developer is not explicitly requesting this way of
 * rendering, this should not be used if the current paint is not
 * a solid colour.
 *
 * If text anti-aliasing is requested by the application, and
 * filling path, an anti-aliasing fill pipe needs to
 * be invoked.
 * This involves making some of the same decisions as in the
 * validatePipe call, which may be in a SurfaceData subclass, so
 * its awkward to always ensure that the correct pipe is used.
 * The easiest thing, rather than reproducing much of that logic
 * is to call validatePipe() which works but is expensive, although
 * probably not compared to the cost of filling the path.
 * Note if AA hint is ON but text-AA hint is OFF this logic will
 * produce AA text which perhaps isn't what the user expected.
 * Note that the glyphvector obeys its FRC, not the G2D.
 */

public class OutlineTextRenderer implements TextPipe {

    // Text with a height greater than the threshhold will be
    // drawn via this pipe.
    public static final int THRESHHOLD = 100;

    public void drawChars(SunGraphics2D g2d,
                          char data[], int offset, int length,
                          int x, int y) {

        String s = new String(data, offset, length);
        drawString(g2d, s, x, y);
    }

    public void drawString(SunGraphics2D g2d, String str, double x, double y) {

        if ("".equals(str)) {
            return; // TextLayout constructor throws IAE on "".
        }
        TextLayout tl = new TextLayout(str, g2d.getFont(),
                                       g2d.getFontRenderContext());
        Shape s = tl.getOutline(AffineTransform.getTranslateInstance(x, y));

        int textAAHint = g2d.getFontInfo().aaHint;

        int prevaaHint = - 1;
        if (textAAHint != SunHints.INTVAL_TEXT_ANTIALIAS_OFF &&
            g2d.antialiasHint != SunHints.INTVAL_ANTIALIAS_ON) {
            prevaaHint = g2d.antialiasHint;
            g2d.antialiasHint =  SunHints.INTVAL_ANTIALIAS_ON;
            g2d.validatePipe();
        } else if (textAAHint == SunHints.INTVAL_TEXT_ANTIALIAS_OFF
            && g2d.antialiasHint != SunHints.INTVAL_ANTIALIAS_OFF) {
            prevaaHint = g2d.antialiasHint;
            g2d.antialiasHint =  SunHints.INTVAL_ANTIALIAS_OFF;
            g2d.validatePipe();
        }

        g2d.fill(s);

        if (prevaaHint != -1) {
             g2d.antialiasHint = prevaaHint;
             g2d.validatePipe();
        }
    }

    public void drawGlyphVector(SunGraphics2D g2d, GlyphVector gv,
                                float x, float y) {


        Shape s = gv.getOutline(x, y);
        int prevaaHint = - 1;
        FontRenderContext frc = gv.getFontRenderContext();
        boolean aa = frc.isAntiAliased();

        /* aa will be true if any AA mode has been specified.
         * ie for LCD and 'gasp' modes too.
         * We will check if 'gasp' has resolved AA to be "OFF", and
         * in all other cases (ie AA ON and all LCD modes) use AA outlines.
         */
        if (aa) {
            if (g2d.getGVFontInfo(gv.getFont(), frc).aaHint ==
                SunHints.INTVAL_TEXT_ANTIALIAS_OFF) {
                aa = false;
            }
        }

        if (aa && g2d.antialiasHint != SunHints.INTVAL_ANTIALIAS_ON) {
            prevaaHint = g2d.antialiasHint;
            g2d.antialiasHint =  SunHints.INTVAL_ANTIALIAS_ON;
            g2d.validatePipe();
        } else if (!aa && g2d.antialiasHint != SunHints.INTVAL_ANTIALIAS_OFF) {
            prevaaHint = g2d.antialiasHint;
            g2d.antialiasHint =  SunHints.INTVAL_ANTIALIAS_OFF;
            g2d.validatePipe();
        }

        g2d.fill(s);

        if (prevaaHint != -1) {
             g2d.antialiasHint = prevaaHint;
             g2d.validatePipe();
        }
    }
}
