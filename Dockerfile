FROM python:3.12-slim
WORKDIR /app
COPY app.py .
ENV PYTHONUNBUFFERED=1 PRESS_DB=/data/press.db HOST=0.0.0.0 PORT=8000
RUN mkdir -p /data
VOLUME /data
EXPOSE 8000
CMD ["python", "app.py", "--no-browser"]
