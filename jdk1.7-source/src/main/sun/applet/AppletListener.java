/*
 * Copyright (c) 1997, Oracle and/or its affiliates. All rights reserved.
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

package sun.applet;

import java.util.EventListener;

/**
 * Applet Listener interface.  This interface is to be implemented
 * by objects interested in AppletEvents.
 *
 * @author  Sunita Mani
 */

public interface AppletListener extends EventListener {
    public void appletStateChanged(AppletEvent e);
}
