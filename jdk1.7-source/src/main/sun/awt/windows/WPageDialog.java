/*
 * Copyright (c) 2003, 2007, Oracle and/or its affiliates. All rights reserved.
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

package sun.awt.windows;

import java.awt.Container;
import java.awt.Dialog;
import java.awt.Frame;
import java.awt.Toolkit;
import java.awt.peer.ComponentPeer;
import java.awt.print.PrinterJob;
import java.awt.print.PageFormat;
import java.awt.print.Printable;

public class WPageDialog extends WPrintDialog {
    static {
        initIDs();
    }

    PageFormat page;
    Printable painter;

    WPageDialog(Frame parent, PrinterJob control, PageFormat page, Printable painter) {
        super(parent, control);
        this.page = page;
        this.painter = painter;
    }


    WPageDialog(Dialog parent, PrinterJob control, PageFormat page, Printable painter) {
        super(parent, control);
        this.page = page;
        this.painter = painter;
    }

    public void addNotify() {
        synchronized(getTreeLock()) {
            Container parent = getParent();
            if (parent != null && parent.getPeer() == null) {
                parent.addNotify();
            }

            if (getPeer() == null) {
                ComponentPeer peer = ((WToolkit)Toolkit.getDefaultToolkit()).
                    createWPageDialog(this);
                setPeer(peer);
            }
            super.addNotify();
        }
    }

    /**
     * Initialize JNI field and method ids
     */
    private static native void initIDs();
}
