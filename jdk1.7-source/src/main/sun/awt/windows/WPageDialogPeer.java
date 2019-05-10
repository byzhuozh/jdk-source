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

public class WPageDialogPeer extends WPrintDialogPeer {

    WPageDialogPeer(WPageDialog target) {
        super(target);
    }

    /**
     * Displays the page setup dialog placing the user's
     * settings into target's 'page'.
     */
    private native boolean _show();

    public void show() {
        new Thread(new Runnable() {
                public void run() {
                    // Call pageSetup even with no printer installed, this
                    // will display Windows error dialog and return false.
                    try {
                        ((WPrintDialog)target).setRetVal(_show());
                    } catch (Exception e) {
                     // No exception should be thrown by native dialog code,
                     // but if it is we need to trap it so the thread does
                     // not hide is called and the thread doesn't hang.
                    }
                    ((WPrintDialog)target).hide();
                }
            }).start();
    }
}
