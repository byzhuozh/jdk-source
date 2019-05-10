/*
 * Copyright (c) 1996, 2007, Oracle and/or its affiliates. All rights reserved.
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

import java.awt.*;
import java.awt.peer.*;
import java.awt.event.ItemEvent;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;
import java.awt.event.WindowAdapter;
import sun.awt.SunToolkit;

class WChoicePeer extends WComponentPeer implements ChoicePeer {

    // WComponentPeer overrides

    public Dimension getMinimumSize() {
        FontMetrics fm = getFontMetrics(((Choice)target).getFont());
        Choice c = (Choice)target;
        int w = 0;
        for (int i = c.getItemCount() ; i-- > 0 ;) {
            w = Math.max(fm.stringWidth(c.getItem(i)), w);
        }
        return new Dimension(28 + w, Math.max(fm.getHeight() + 6, 15));
    }
    public boolean isFocusable() {
        return true;
    }

    // ChoicePeer implementation

    public native void select(int index);

    public void add(String item, int index) {
        addItem(item, index);
    }

    public boolean shouldClearRectBeforePaint() {
        return false;
    }

    public native void removeAll();
    public native void remove(int index);

    /**
     * DEPRECATED, but for now, called by add(String, int).
     */
    public void addItem(String item, int index) {
        addItems(new String[] {item}, index);
    }
    public native void addItems(String[] items, int index);

    public synchronized native void reshape(int x, int y, int width, int height);

    private WindowListener windowListener;

    // Toolkit & peer internals

    WChoicePeer(Choice target) {
        super(target);
    }

    native void create(WComponentPeer parent);

    void initialize() {
        Choice opt = (Choice)target;
        int itemCount = opt.getItemCount();
        if (itemCount > 0) {
            String[] items = new String[itemCount];
            for (int i=0; i < itemCount; i++) {
                items[i] = opt.getItem(i);
            }
            addItems(items, 0);
            if (opt.getSelectedIndex() >= 0) {
                select(opt.getSelectedIndex());
            }
        }

        Window parentWindow = SunToolkit.getContainingWindow((Component)target);
        if (parentWindow != null) {
            WWindowPeer wpeer = (WWindowPeer)parentWindow.getPeer();
            if (wpeer != null) {
                windowListener = new WindowAdapter() {
                        public void windowIconified(WindowEvent e) {
                            closeList();
                        }
                        public void windowClosing(WindowEvent e) {
                            closeList();
                        }
                    };
                wpeer.addWindowListener(windowListener);
            }
        }
        super.initialize();
    }

    protected void disposeImpl() {
        // TODO: we should somehow reset the listener when the choice
        // is moved to another toplevel without destroying its peer.
        Window parentWindow = SunToolkit.getContainingWindow((Component)target);
        if (parentWindow != null) {
            WWindowPeer wpeer = (WWindowPeer)parentWindow.getPeer();
            if (wpeer != null) {
                wpeer.removeWindowListener(windowListener);
            }
        }
        super.disposeImpl();
    }

    // native callbacks

    void handleAction(final int index) {
        final Choice c = (Choice)target;
        WToolkit.executeOnEventHandlerThread(c, new Runnable() {
            public void run() {
                c.select(index);
                postEvent(new ItemEvent(c, ItemEvent.ITEM_STATE_CHANGED,
                                c.getItem(index), ItemEvent.SELECTED));
            }
        });
    }

    int getDropDownHeight() {
        Choice c = (Choice)target;
        FontMetrics fm = getFontMetrics(c.getFont());
        int maxItems = Math.min(c.getItemCount(), 8);
        return fm.getHeight() * maxItems;
    }

    /**
     * DEPRECATED
     */
    public Dimension minimumSize() {
            return getMinimumSize();
    }

    native void closeList();
}
