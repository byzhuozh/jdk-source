/*
 * Copyright (c) 2008, Oracle and/or its affiliates. All rights reserved.
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

package sun.awt;

import java.awt.AWTEvent;
import java.awt.EventQueue;


public class EventQueueDelegate {
    private static final Object EVENT_QUEUE_DELEGATE_KEY =
        new StringBuilder("EventQueueDelegate.Delegate");

    public static void setDelegate(Delegate delegate) {
        AppContext.getAppContext().put(EVENT_QUEUE_DELEGATE_KEY, delegate);
    }
    public static Delegate getDelegate() {
        return
          (Delegate) AppContext.getAppContext().get(EVENT_QUEUE_DELEGATE_KEY);
    }
    public interface Delegate {
        /**
         * This method allows for changing {@code EventQueue} events order.
         *
         * @param eventQueue current {@code EventQueue}
         * @return next {@code event} for the {@code EventDispatchThread}
         */

        public AWTEvent getNextEvent(EventQueue eventQueue) throws InterruptedException;

        /**
         * Notifies delegate before EventQueue.dispatch method.
         *
         * Note: this method may mutate the event
         *
         * @param event  to be dispatched by {@code dispatch} method
         * @return handle to be passed to {@code afterDispatch} method
         */
        public Object beforeDispatch(AWTEvent event) throws InterruptedException;

        /**
         * Notifies delegate after EventQueue.dispatch method.
         *
         * @param event {@code event} dispatched by the {@code dispatch} method
         * @param handle object which came from {@code beforeDispatch} method
         */
        public void afterDispatch(AWTEvent event, Object handle) throws InterruptedException;
    }
}
