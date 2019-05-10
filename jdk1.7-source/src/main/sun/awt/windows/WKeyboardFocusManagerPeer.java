/*
 * Copyright (c) 2009, Oracle and/or its affiliates. All rights reserved.
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

import java.awt.KeyboardFocusManager;
import java.awt.Window;
import java.awt.Component;
import java.awt.peer.ComponentPeer;
import sun.awt.KeyboardFocusManagerPeerImpl;
import sun.awt.CausedFocusEvent;

class WKeyboardFocusManagerPeer extends KeyboardFocusManagerPeerImpl {
    static native void setNativeFocusOwner(ComponentPeer peer);
    static native Component getNativeFocusOwner();
    static native Window getNativeFocusedWindow();

    WKeyboardFocusManagerPeer(KeyboardFocusManager manager) {
        super(manager);
    }

    @Override
    public void setCurrentFocusOwner(Component comp) {
        setNativeFocusOwner(comp != null ? comp.getPeer() : null);
    }

    @Override
    public Component getCurrentFocusOwner() {
        return getNativeFocusOwner();
    }

    @Override
    public Window getCurrentFocusedWindow() {
        return getNativeFocusedWindow();
    }

    public static boolean deliverFocus(Component lightweightChild,
                                       Component target,
                                       boolean temporary,
                                       boolean focusedWindowChangeAllowed,
                                       long time,
                                       CausedFocusEvent.Cause cause)
    {
        // TODO: do something to eliminate this forwarding
        return KeyboardFocusManagerPeerImpl.deliverFocus(lightweightChild,
                                                         target,
                                                         temporary,
                                                         focusedWindowChangeAllowed,
                                                         time,
                                                         cause,
                                                         getNativeFocusOwner());
    }
}
