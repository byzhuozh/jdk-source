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


package sun.util.logging;

/**
 * A proxy interface for the java.util.logging support.
 *
 * @see sun.util.logging.LoggingSupport
 */
public interface LoggingProxy {
    // Methods to bridge java.util.logging.Logger methods
    public Object getLogger(String name);

    public Object getLevel(Object logger);

    public void setLevel(Object logger, Object newLevel);

    public boolean isLoggable(Object logger, Object level);

    public void log(Object logger, Object level, String msg);

    public void log(Object logger, Object level, String msg, Throwable t);

    public void log(Object logger, Object level, String msg, Object... params);

    // Methods to bridge java.util.logging.LoggingMXBean methods
    public java.util.List<String> getLoggerNames();

    public String getLoggerLevel(String loggerName);

    public void setLoggerLevel(String loggerName, String levelName);

    public String getParentLoggerName(String loggerName);

    // Methods to bridge Level.parse() and Level.getName() method
    public Object parseLevel(String levelName);

    public String getLevelName(Object level);

    // return the logging property
    public String getProperty(String key);
}
